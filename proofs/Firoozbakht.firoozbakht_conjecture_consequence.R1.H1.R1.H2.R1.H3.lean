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

namespace OMA.PrimeSieveBase

def ranged (start width trial : ℕ) : List ℕ :=
  (List.range' start width).filter (checks trial)

theorem mem_ranged {q start width trial : ℕ} (lo : start≤q) (hi : q<start+width)
    (prime : q.Prime) (odd : q%2=1) : q ∈ ranged start width trial := by
  have h := mem_smallPrimes (bound:=q) (trial:=trial) (le_refl _) prime odd
  unfold smallPrimes at h
  exact List.mem_filter.mpr ⟨List.mem_range'_1.mpr ⟨lo,hi⟩,(List.mem_filter.mp h).2⟩

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

namespace OMA.UpperPrimeCheckpoint

open OMA.PrimePopulation OMA.PrimeProgression

private def part0 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def check0 : PLift (OMA.PrimeSieveBase.ranged 0 2048 97 = part0) :=
  ⟨by decide +kernel⟩
private def part1 : List ℕ := [2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def check1 : PLift (OMA.PrimeSieveBase.ranged 2048 2048 97 = part1) :=
  ⟨by decide +kernel⟩
private def part2 : List ℕ := [4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def check2 : PLift (OMA.PrimeSieveBase.ranged 4096 2048 97 = part2) :=
  ⟨by decide +kernel⟩
private def part3 : List ℕ := [6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def check3 : PLift (OMA.PrimeSieveBase.ranged 6144 2048 97 = part3) :=
  ⟨by decide +kernel⟩
private def part4 : List ℕ := [8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def check4 : PLift (OMA.PrimeSieveBase.ranged 8192 1294 97 = part4) :=
  ⟨by decide +kernel⟩

private def primes : List ℕ := part0 ++ (part1 ++ (part2 ++ (part3 ++ (part4))))

private theorem complete : ∀ p ≤ 9485, p.Prime → p%2=1 → p∈primes := by
  intro p bound prime odd
  unfold primes
  by_cases h0 : p<2048
  · exact List.mem_append.mpr (Or.inl (check0.down ▸ OMA.PrimeSieveBase.mem_ranged (start := 0) (width := 2048) (trial := 97) (by omega) (by omega) prime odd))
  by_cases h1 : p<4096
  · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl (check1.down ▸ OMA.PrimeSieveBase.mem_ranged (start := 2048) (width := 2048) (trial := 97) (by omega) (by omega) prime odd))))
  by_cases h2 : p<6144
  · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl (check2.down ▸ OMA.PrimeSieveBase.mem_ranged (start := 4096) (width := 2048) (trial := 97) (by omega) (by omega) prime odd))))))
  by_cases h3 : p<8192
  · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl (check3.down ▸ OMA.PrimeSieveBase.mem_ranged (start := 6144) (width := 2048) (trial := 97) (by omega) (by omega) prime odd))))))))
  exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr ((check4.down ▸ OMA.PrimeSieveBase.mem_ranged (start := 8192) (width := 1294) (trial := 97) (by omega) (by omega) prime odd)))))))))

private theorem joinRows (xs : List Row) (offset count : ℕ)
    (first : ∀ row ∈ (xs.drop offset).take count, row.2.2.1 ≤ row.1.primeCounting)
    (later : ∀ row ∈ xs.drop (offset+count), row.2.2.1 ≤ row.1.primeCounting) :
    ∀ row ∈ xs.drop offset, row.2.2.1 ≤ row.1.primeCounting := by
  have after : ∀ row ∈ (xs.drop offset).drop count, row.2.2.1 ≤ row.1.primeCounting := by
    simpa only [List.drop_drop,Nat.add_comm] using later
  have joined := List.forall_mem_append.mpr ⟨first,after⟩
  rw [List.take_append_drop] at joined
  exact joined

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate00 : PLift (checkedSegment primes 20 14 0 524288 = 82024) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state00 : 82024 ≤ oddCount 524288 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 0) (width := 524288) (current := 0) (by decide) (by decide) (by decide) (Nat.zero_le _)
  rw [gate00.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate01 : PLift (checkedSegment primes 20 14 524288 524288 = 73586) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state01 : 155610 ≤ oddCount 1048576 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 524288) (width := 524288) (current := 82024) (by decide) (by decide) (by decide) state00
  rw [gate01.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate02 : PLift (checkedSegment primes 20 14 1048576 524288 = 70938) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state02 : 226548 ≤ oddCount 1572864 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 1048576) (width := 524288) (current := 155610) (by decide) (by decide) (by decide) state01
  rw [gate02.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate03 : PLift (checkedSegment primes 20 14 1572864 524288 = 69398) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state03 : 295946 ≤ oddCount 2097152 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 1572864) (width := 524288) (current := 226548) (by decide) (by decide) (by decide) state02
  rw [gate03.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate04 : PLift (checkedSegment primes 20 14 2097152 524288 = 68248) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state04 : 364194 ≤ oddCount 2621440 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 2097152) (width := 524288) (current := 295946) (by decide) (by decide) (by decide) state03
  rw [gate04.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate05 : PLift (checkedSegment primes 20 14 2621440 524288 = 67307) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state05 : 431501 ≤ oddCount 3145728 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 2621440) (width := 524288) (current := 364194) (by decide) (by decide) (by decide) state04
  rw [gate05.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate06 : PLift (checkedSegment primes 20 14 3145728 524288 = 66675) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state06 : 498176 ≤ oddCount 3670016 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 3145728) (width := 524288) (current := 431501) (by decide) (by decide) (by decide) state05
  rw [gate06.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate07 : PLift (checkedSegment primes 20 14 3670016 524288 = 65986) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state07 : 564162 ≤ oddCount 4194304 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 3670016) (width := 524288) (current := 498176) (by decide) (by decide) (by decide) state06
  rw [gate07.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate08 : PLift (checkedSegment primes 20 14 4194304 524288 = 65523) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state08 : 629685 ≤ oddCount 4718592 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 4194304) (width := 524288) (current := 564162) (by decide) (by decide) (by decide) state07
  rw [gate08.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate09 : PLift (checkedSegment primes 20 14 4718592 524288 = 65030) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state09 : 694715 ≤ oddCount 5242880 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 4718592) (width := 524288) (current := 629685) (by decide) (by decide) (by decide) state08
  rw [gate09.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate10 : PLift (checkedSegment primes 20 14 5242880 524288 = 64685) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state10 : 759400 ≤ oddCount 5767168 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 5242880) (width := 524288) (current := 694715) (by decide) (by decide) (by decide) state09
  rw [gate10.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate11 : PLift (checkedSegment primes 20 14 5767168 524288 = 64348) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state11 : 823748 ≤ oddCount 6291456 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 5767168) (width := 524288) (current := 759400) (by decide) (by decide) (by decide) state10
  rw [gate11.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate12 : PLift (checkedSegment primes 20 14 6291456 524288 = 63893) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state12 : 887641 ≤ oddCount 6815744 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 6291456) (width := 524288) (current := 823748) (by decide) (by decide) (by decide) state11
  rw [gate12.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate13 : PLift (checkedSegment primes 20 14 6815744 524288 = 63709) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state13 : 951350 ≤ oddCount 7340032 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 6815744) (width := 524288) (current := 887641) (by decide) (by decide) (by decide) state12
  rw [gate13.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate14 : PLift (checkedSegment primes 20 14 7340032 524288 = 63382) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state14 : 1014732 ≤ oddCount 7864320 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 7340032) (width := 524288) (current := 951350) (by decide) (by decide) (by decide) state13
  rw [gate14.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate15 : PLift (checkedSegment primes 20 14 7864320 524288 = 63138) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state15 : 1077870 ≤ oddCount 8388608 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 7864320) (width := 524288) (current := 1014732) (by decide) (by decide) (by decide) state14
  rw [gate15.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate16 : PLift (checkedSegment primes 20 14 8388608 524288 = 63008) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state16 : 1140878 ≤ oddCount 8912896 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 8388608) (width := 524288) (current := 1077870) (by decide) (by decide) (by decide) state15
  rw [gate16.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate17 : PLift (checkedSegment primes 20 14 8912896 524288 = 62690) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state17 : 1203568 ≤ oddCount 9437184 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 8912896) (width := 524288) (current := 1140878) (by decide) (by decide) (by decide) state16
  rw [gate17.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate18 : PLift (checkedSegment primes 20 14 9437184 524288 = 62442) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state18 : 1266010 ≤ oddCount 9961472 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 9437184) (width := 524288) (current := 1203568) (by decide) (by decide) (by decide) state17
  rw [gate18.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate19 : PLift (checkedSegment primes 20 14 9961472 524288 = 62219) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state19 : 1328229 ≤ oddCount 10485760 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 9961472) (width := 524288) (current := 1266010) (by decide) (by decide) (by decide) state18
  rw [gate19.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate20 : PLift (checkedSegment primes 20 14 10485760 524288 = 62209) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state20 : 1390438 ≤ oddCount 11010048 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 10485760) (width := 524288) (current := 1328229) (by decide) (by decide) (by decide) state19
  rw [gate20.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate21 : PLift (checkedSegment primes 20 14 11010048 524288 = 61874) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state21 : 1452312 ≤ oddCount 11534336 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 11010048) (width := 524288) (current := 1390438) (by decide) (by decide) (by decide) state20
  rw [gate21.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate22 : PLift (checkedSegment primes 20 14 11534336 524288 = 61709) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state22 : 1514021 ≤ oddCount 12058624 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 11534336) (width := 524288) (current := 1452312) (by decide) (by decide) (by decide) state21
  rw [gate22.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate23 : PLift (checkedSegment primes 20 14 12058624 524288 = 61639) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state23 : 1575660 ≤ oddCount 12582912 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 12058624) (width := 524288) (current := 1514021) (by decide) (by decide) (by decide) state22
  rw [gate23.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate24 : PLift (checkedSegment primes 20 14 12582912 524288 = 61393) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state24 : 1637053 ≤ oddCount 13107200 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 12582912) (width := 524288) (current := 1575660) (by decide) (by decide) (by decide) state23
  rw [gate24.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate25 : PLift (checkedSegment primes 20 14 13107200 524288 = 61362) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state25 : 1698415 ≤ oddCount 13631488 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 13107200) (width := 524288) (current := 1637053) (by decide) (by decide) (by decide) state24
  rw [gate25.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate26 : PLift (checkedSegment primes 20 14 13631488 524288 = 61235) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state26 : 1759650 ≤ oddCount 14155776 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 14)
    (base := 13631488) (width := 524288) (current := 1698415) (by decide) (by decide) (by decide) state25
  rw [gate26.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate27 : PLift (checkedSegment primes 20 13 14155776 163703 = 19061) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state27 : 1778711 ≤ oddCount 14319479 := by
  have h := checkedSegment_add complete (markDepth := 20) (popDepth := 13)
    (base := 14155776) (width := 163703) (current := 1759650) (by decide) (by decide) (by decide) state26
  rw [gate27.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate28 : PLift (checkRows 14319479 513997 (composite primes 20 14319479 513997) 0 1778711 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk070_data) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk070_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts28 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk070_data), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 14319479) (width := 513997)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk070_data) (left := 0) (count := 1778711) state27 gate28.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked28 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk070_data), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts28 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state28 : 1838410 ≤ oddCount 14833476 := by
  let row : Row := (29666951,29682983,1838411,6354)
  have hmem : row∈(Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk070_data) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk070_data]; decide
  have h := (counts28 row hmem).2
  have slot : (row.1+1)/2 = 14833476 := by decide
  have value : row.2.2.1 = 1838411 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate29 : PLift (checkRows 14833476 593493 (composite primes 20 14833476 593493) 0 1838410 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk071_data) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk071_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts29 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk071_data), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 14833476) (width := 593493)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk071_data) (left := 0) (count := 1838410) state28 gate29.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked29 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk071_data), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts29 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state29 : 1907544 ≤ oddCount 15426969 := by
  let row : Row := (30853938,30876955,1907545,6369)
  have hmem : row∈(Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk071_data) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk071_data]; decide
  have h := (counts29 row hmem).2
  have slot : (row.1+1)/2 = 15426969 := by decide
  have value : row.2.2.1 = 1907545 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate30 : PLift (checkRows 15426969 610882 (composite primes 20 15426969 610882) 0 1907544 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk072_data) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk072_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts30 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk072_data), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 15426969) (width := 610882)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk072_data) (left := 0) (count := 1907544) state29 gate30.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked30 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk072_data), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts30 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state30 : 1978169 ≤ oddCount 16037851 := by
  let row : Row := (32075701,32095381,1978170,6383)
  have hmem : row∈(Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk072_data) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk072_data]; decide
  have h := (counts30 row hmem).2
  have slot : (row.1+1)/2 = 16037851 := by decide
  have value : row.2.2.1 = 1978170 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate31 : PLift (checkRows 16037851 632334 (composite primes 20 16037851 632334) 0 1978169 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk073_data) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk073_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts31 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk073_data), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 16037851) (width := 632334)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk073_data) (left := 0) (count := 1978169) state30 gate31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked31 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk073_data), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts31 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state31 : 2051338 ≤ oddCount 16670185 := by
  let row : Row := (33340370,33360551,2051339,6397)
  have hmem : row∈(Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk073_data) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk073_data]; decide
  have h := (counts31 row hmem).2
  have slot : (row.1+1)/2 = 16670185 := by decide
  have value : row.2.2.1 = 2051339 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate32 : PLift (checkRows 16670185 645059 (composite primes 20 16670185 645059) 0 2051338 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk074_data) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk074_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts32 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk074_data), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 16670185) (width := 645059)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk074_data) (left := 0) (count := 2051338) state31 gate32.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked32 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk074_data), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts32 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state32 : 2125535 ≤ oddCount 17315244 := by
  let row : Row := (34630488,34648043,2125536,6411)
  have hmem : row∈(Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk074_data) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk074_data]; decide
  have h := (counts32 row hmem).2
  have slot : (row.1+1)/2 = 17315244 := by decide
  have value : row.2.2.1 = 2125536 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate33 : PLift (checkRows 17315244 566224 (composite primes 20 17315244 566224) 0 2125535 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk075_data) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk075_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts33 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk075_data), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 17315244) (width := 566224)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk075_data) (left := 0) (count := 2125535) state32 gate33.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked33 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk075_data), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts33 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state33 : 2190648 ≤ oddCount 17881468 := by
  let row : Row := (35762936,35780853,2190649,6423)
  have hmem : row∈(Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk075_data) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk075_data]; decide
  have h := (counts33 row hmem).2
  have slot : (row.1+1)/2 = 17881468 := by decide
  have value : row.2.2.1 = 2190649 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate34 : PLift (checkRows 17881468 588206 (composite primes 20 17881468 588206) 0 2190648 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk076_data) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk076_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts34 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk076_data), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 17881468) (width := 588206)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk076_data) (left := 0) (count := 2190648) state33 gate34.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked34 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk076_data), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts34 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state34 : 2258119 ≤ oddCount 18469674 := by
  let row : Row := (36939347,36956498,2258120,6435)
  have hmem : row∈(Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk076_data) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk076_data]; decide
  have h := (counts34 row hmem).2
  have slot : (row.1+1)/2 = 18469674 := by decide
  have value : row.2.2.1 = 2258120 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate35 : PLift (checkRows 18469674 588782 (composite primes 20 18469674 588782) 0 2258119 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk077_data) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk077_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts35 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk077_data), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 18469674) (width := 588782)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk077_data) (left := 0) (count := 2258119) state34 gate35.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked35 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk077_data), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts35 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state35 : 2325706 ≤ oddCount 19058456 := by
  let row : Row := (38116912,38138444,2325707,6447)
  have hmem : row∈(Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk077_data) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk077_data]; decide
  have h := (counts35 row hmem).2
  have slot : (row.1+1)/2 = 19058456 := by decide
  have value : row.2.2.1 = 2325707 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate36 : PLift (checkRows 19058456 674761 (composite primes 20 19058456 674761) 0 2325706 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk078_data) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk078_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts36 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk078_data), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 19058456) (width := 674761)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk078_data) (left := 0) (count := 2325706) state35 gate36.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked36 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk078_data), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts36 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state36 : 2403157 ≤ oddCount 19733217 := by
  let row : Row := (39466433,39486873,2403158,6459)
  have hmem : row∈(Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk078_data) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk078_data]; decide
  have h := (counts36 row hmem).2
  have slot : (row.1+1)/2 = 19733217 := by decide
  have value : row.2.2.1 = 2403158 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate37 : PLift (checkRows 19733217 688945 (composite primes 20 19733217 688945) 0 2403157 (List.take 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts37 :
    ∀ row ∈ (List.take 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 19733217) (width := 688945)
    (by decide) (by decide) (List.take 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data)) (left := 0) (count := 2403157) state36 gate37.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked37 :
    ∀ row ∈ (List.take 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts37 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state37 : 2481958 ≤ oddCount 20422162 := by
  let row : Row := (40844323,40869318,2481959,6472)
  have hmem : row∈(List.take 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data]; decide
  have h := (counts37 row hmem).2
  have slot : (row.1+1)/2 = 20422162 := by decide
  have value : row.2.2.1 = 2481959 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate38 : PLift (checkRows 20422162 85155 (composite primes 20 20422162 85155) 0 2481958 (List.drop 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts38 :
    ∀ row ∈ (List.drop 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 20422162) (width := 85155)
    (by decide) (by decide) (List.drop 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data)) (left := 0) (count := 2481958) state37 gate38.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked38 :
    ∀ row ∈ (List.drop 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts38 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state38 : 2491591 ≤ oddCount 20507317 := by
  let row : Row := (41014634,41041477,2491592,6474)
  have hmem : row∈(List.drop 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data]; decide
  have h := (counts38 row hmem).2
  have slot : (row.1+1)/2 = 20507317 := by decide
  have value : row.2.2.1 = 2491592 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate39 : PLift (checkRows 20507317 689788 (composite primes 20 20507317 689788) 0 2491591 (List.take 58 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts39 :
    ∀ row ∈ (List.take 58 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 20507317) (width := 689788)
    (by decide) (by decide) (List.take 58 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data)) (left := 0) (count := 2491591) state38 gate39.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked39 :
    ∀ row ∈ (List.take 58 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts39 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state39 : 2570160 ≤ oddCount 21197105 := by
  let row : Row := (42394209,42419444,2570161,6486)
  have hmem : row∈(List.take 58 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data]; decide
  have h := (counts39 row hmem).2
  have slot : (row.1+1)/2 = 21197105 := by decide
  have value : row.2.2.1 = 2570161 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate40 : PLift (checkRows 21197105 71639 (composite primes 20 21197105 71639) 0 2570160 (List.drop 58 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts40 :
    ∀ row ∈ (List.drop 58 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 21197105) (width := 71639)
    (by decide) (by decide) (List.drop 58 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data)) (left := 0) (count := 2570160) state39 gate40.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked40 :
    ∀ row ∈ (List.drop 58 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts40 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state40 : 2578310 ≤ oddCount 21268744 := by
  let row : Row := (42537488,42560960,2578311,6487)
  have hmem : row∈(List.drop 58 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data]; decide
  have h := (counts40 row hmem).2
  have slot : (row.1+1)/2 = 21268744 := by decide
  have value : row.2.2.1 = 2578311 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate41 : PLift (checkRows 21268744 688080 (composite primes 20 21268744 688080) 0 2578310 (List.take 59 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts41 :
    ∀ row ∈ (List.take 59 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 21268744) (width := 688080)
    (by decide) (by decide) (List.take 59 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data)) (left := 0) (count := 2578310) state40 gate41.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked41 :
    ∀ row ∈ (List.take 59 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts41 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state41 : 2656392 ≤ oddCount 21956824 := by
  let row : Row := (43913648,43936472,2656393,6499)
  have hmem : row∈(List.take 59 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data]; decide
  have h := (counts41 row hmem).2
  have slot : (row.1+1)/2 = 21956824 := by decide
  have value : row.2.2.1 = 2656393 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate42 : PLift (checkRows 21956824 56038 (composite primes 20 21956824 56038) 0 2656392 (List.drop 59 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts42 :
    ∀ row ∈ (List.drop 59 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 21956824) (width := 56038)
    (by decide) (by decide) (List.drop 59 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data)) (left := 0) (count := 2656392) state41 gate42.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked42 :
    ∀ row ∈ (List.drop 59 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts42 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state42 : 2662834 ≤ oddCount 22012862 := by
  let row : Row := (44025723,44050255,2662835,6500)
  have hmem : row∈(List.drop 59 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data]; decide
  have h := (counts42 row hmem).2
  have slot : (row.1+1)/2 = 22012862 := by decide
  have value : row.2.2.1 = 2662835 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate43 : PLift (checkRows 22012862 678522 (composite primes 20 22012862 678522) 0 2662834 (List.take 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts43 :
    ∀ row ∈ (List.take 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 22012862) (width := 678522)
    (by decide) (by decide) (List.take 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data)) (left := 0) (count := 2662834) state42 gate43.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked43 :
    ∀ row ∈ (List.take 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts43 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state43 : 2740012 ≤ oddCount 22691384 := by
  let row : Row := (45382768,45408852,2740013,6511)
  have hmem : row∈(List.take 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data]; decide
  have h := (counts43 row hmem).2
  have slot : (row.1+1)/2 = 22691384 := by decide
  have value : row.2.2.1 = 2740013 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate44 : PLift (checkRows 22691384 90797 (composite primes 20 22691384 90797) 0 2740012 (List.drop 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts44 :
    ∀ row ∈ (List.drop 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 22691384) (width := 90797)
    (by decide) (by decide) (List.drop 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data)) (left := 0) (count := 2740012) state43 gate44.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked44 :
    ∀ row ∈ (List.drop 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts44 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state44 : 2750338 ≤ oddCount 22782181 := by
  let row : Row := (45564362,45587450,2750339,6512)
  have hmem : row∈(List.drop 57 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data]; decide
  have h := (counts44 row hmem).2
  have slot : (row.1+1)/2 = 22782181 := by decide
  have value : row.2.2.1 = 2750339 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate45 : PLift (checkRows 22782181 688592 (composite primes 20 22782181 688592) 0 2750338 (List.take 51 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts45 :
    ∀ row ∈ (List.take 51 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 22782181) (width := 688592)
    (by decide) (by decide) (List.take 51 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data)) (left := 0) (count := 2750338) state44 gate45.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked45 :
    ∀ row ∈ (List.take 51 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts45 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state45 : 2828387 ≤ oddCount 23470773 := by
  let row : Row := (46941546,46965639,2828388,6523)
  have hmem : row∈(List.take 51 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data]; decide
  have h := (counts45 row hmem).2
  have slot : (row.1+1)/2 = 23470773 := by decide
  have value : row.2.2.1 = 2828388 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate46 : PLift (checkRows 23470773 177609 (composite primes 20 23470773 177609) 0 2828387 (List.drop 51 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts46 :
    ∀ row ∈ (List.drop 51 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 23470773) (width := 177609)
    (by decide) (by decide) (List.drop 51 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data)) (left := 0) (count := 2828387) state45 gate46.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked46 :
    ∀ row ∈ (List.drop 51 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts46 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state46 : 2848445 ≤ oddCount 23648382 := by
  let row : Row := (47296764,47321916,2848446,6526)
  have hmem : row∈(List.drop 51 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data]; decide
  have h := (counts46 row hmem).2
  have slot : (row.1+1)/2 = 23648382 := by decide
  have value : row.2.2.1 = 2848446 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate47 : PLift (checkRows 23648382 680612 (composite primes 20 23648382 680612) 0 2848445 (List.take 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts47 :
    ∀ row ∈ (List.take 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 23648382) (width := 680612)
    (by decide) (by decide) (List.take 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data)) (left := 0) (count := 2848445) state46 gate47.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked47 :
    ∀ row ∈ (List.take 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts47 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state47 : 2925241 ≤ oddCount 24328994 := by
  let row : Row := (48657988,48685149,2925242,6537)
  have hmem : row∈(List.take 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data]; decide
  have h := (counts47 row hmem).2
  have slot : (row.1+1)/2 = 24328994 := by decide
  have value : row.2.2.1 = 2925242 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate48 : PLift (checkRows 24328994 150844 (composite primes 20 24328994 150844) 0 2925241 (List.drop 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts48 :
    ∀ row ∈ (List.drop 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 24328994) (width := 150844)
    (by decide) (by decide) (List.drop 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data)) (left := 0) (count := 2925241) state47 gate48.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked48 :
    ∀ row ∈ (List.drop 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts48 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state48 : 2942271 ≤ oddCount 24479838 := by
  let row : Row := (48959676,48984565,2942272,6539)
  have hmem : row∈(List.drop 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data]; decide
  have h := (counts48 row hmem).2
  have slot : (row.1+1)/2 = 24479838 := by decide
  have value : row.2.2.1 = 2942272 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate49 : PLift (checkRows 24479838 687416 (composite primes 20 24479838 687416) 0 2942271 (List.take 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts49 :
    ∀ row ∈ (List.take 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 24479838) (width := 687416)
    (by decide) (by decide) (List.take 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data)) (left := 0) (count := 2942271) state48 gate49.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked49 :
    ∀ row ∈ (List.take 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts49 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state49 : 3019990 ≤ oddCount 25167254 := by
  let row : Row := (50334507,50360504,3019991,6549)
  have hmem : row∈(List.take 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data]; decide
  have h := (counts49 row hmem).2
  have slot : (row.1+1)/2 = 25167254 := by decide
  have value : row.2.2.1 = 3019991 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate50 : PLift (checkRows 25167254 162149 (composite primes 20 25167254 162149) 0 3019990 (List.drop 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts50 :
    ∀ row ∈ (List.drop 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 25167254) (width := 162149)
    (by decide) (by decide) (List.drop 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data)) (left := 0) (count := 3019990) state49 gate50.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked50 :
    ∀ row ∈ (List.drop 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts50 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state50 : 3038261 ≤ oddCount 25329403 := by
  let row : Row := (50658805,50689943,3038262,6552)
  have hmem : row∈(List.drop 52 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data]; decide
  have h := (counts50 row hmem).2
  have slot : (row.1+1)/2 = 25329403 := by decide
  have value : row.2.2.1 = 3038262 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate51 : PLift (checkRows 25329403 683779 (composite primes 20 25329403 683779) 0 3038261 (List.take 48 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts51 :
    ∀ row ∈ (List.take 48 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 25329403) (width := 683779)
    (by decide) (by decide) (List.take 48 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data)) (left := 0) (count := 3038261) state50 gate51.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked51 :
    ∀ row ∈ (List.take 48 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts51 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state51 : 3115312 ≤ oddCount 26013182 := by
  let row : Row := (52026363,52051608,3115313,6561)
  have hmem : row∈(List.take 48 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data]; decide
  have h := (counts51 row hmem).2
  have slot : (row.1+1)/2 = 26013182 := by decide
  have value : row.2.2.1 = 3115313 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate52 : PLift (checkRows 26013182 234824 (composite primes 20 26013182 234824) 0 3115312 (List.drop 48 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts52 :
    ∀ row ∈ (List.drop 48 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 26013182) (width := 234824)
    (by decide) (by decide) (List.drop 48 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data)) (left := 0) (count := 3115312) state51 gate52.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked52 :
    ∀ row ∈ (List.drop 48 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts52 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state52 : 3141714 ≤ oddCount 26248006 := by
  let row : Row := (52496012,52526874,3141715,6565)
  have hmem : row∈(List.drop 48 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data]; decide
  have h := (counts52 row hmem).2
  have slot : (row.1+1)/2 = 26248006 := by decide
  have value : row.2.2.1 = 3141715 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate53 : PLift (checkRows 26248006 678210 (composite primes 20 26248006 678210) 0 3141714 (List.take 47 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts53 :
    ∀ row ∈ (List.take 47 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 26248006) (width := 678210)
    (by decide) (by decide) (List.take 47 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data)) (left := 0) (count := 3141714) state52 gate53.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked53 :
    ∀ row ∈ (List.take 47 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts53 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state53 : 3217854 ≤ oddCount 26926216 := by
  let row : Row := (53852432,53878534,3217855,6574)
  have hmem : row∈(List.take 47 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data]; decide
  have h := (counts53 row hmem).2
  have slot : (row.1+1)/2 = 26926216 := by decide
  have value : row.2.2.1 = 3217855 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate54 : PLift (checkRows 26926216 241146 (composite primes 20 26926216 241146) 0 3217854 (List.drop 47 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts54 :
    ∀ row ∈ (List.drop 47 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 26926216) (width := 241146)
    (by decide) (by decide) (List.drop 47 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data)) (left := 0) (count := 3217854) state53 gate54.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked54 :
    ∀ row ∈ (List.drop 47 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts54 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state54 : 3244946 ≤ oddCount 27167362 := by
  let row : Row := (54334723,54367407,3244947,6578)
  have hmem : row∈(List.drop 47 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data]; decide
  have h := (counts54 row hmem).2
  have slot : (row.1+1)/2 = 27167362 := by decide
  have value : row.2.2.1 = 3244947 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate55 : PLift (checkRows 27167362 676570 (composite primes 20 27167362 676570) 0 3244946 (List.take 49 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts55 :
    ∀ row ∈ (List.take 49 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 27167362) (width := 676570)
    (by decide) (by decide) (List.take 49 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data)) (left := 0) (count := 3244946) state54 gate55.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked55 :
    ∀ row ∈ (List.take 49 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts55 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state55 : 3320795 ≤ oddCount 27843932 := by
  let row : Row := (55687863,55719395,3320796,6587)
  have hmem : row∈(List.take 49 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data]; decide
  have h := (counts55 row hmem).2
  have slot : (row.1+1)/2 = 27843932 := by decide
  have value : row.2.2.1 = 3320796 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate56 : PLift (checkRows 27843932 217303 (composite primes 20 27843932 217303) 0 3320795 (List.drop 49 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts56 :
    ∀ row ∈ (List.drop 49 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 27843932) (width := 217303)
    (by decide) (by decide) (List.drop 49 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data)) (left := 0) (count := 3320795) state55 gate56.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked56 :
    ∀ row ∈ (List.drop 49 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts56 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state56 : 3345241 ≤ oddCount 28061235 := by
  let row : Row := (56122469,56147745,3345242,6589)
  have hmem : row∈(List.drop 49 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data]; decide
  have h := (counts56 row hmem).2
  have slot : (row.1+1)/2 = 28061235 := by decide
  have value : row.2.2.1 = 3345242 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate57 : PLift (checkRows 28061235 675981 (composite primes 20 28061235 675981) 0 3345241 (List.take 45 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts57 :
    ∀ row ∈ (List.take 45 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 28061235) (width := 675981)
    (by decide) (by decide) (List.take 45 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data)) (left := 0) (count := 3345241) state56 gate57.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked57 :
    ∀ row ∈ (List.take 45 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts57 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state57 : 3421023 ≤ oddCount 28737216 := by
  let row : Row := (57474431,57503324,3421024,6598)
  have hmem : row∈(List.take 45 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data]; decide
  have h := (counts57 row hmem).2
  have slot : (row.1+1)/2 = 28737216 := by decide
  have value : row.2.2.1 = 3421024 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate58 : PLift (checkRows 28737216 291961 (composite primes 20 28737216 291961) 0 3421023 (List.drop 45 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts58 :
    ∀ row ∈ (List.drop 45 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 28737216) (width := 291961)
    (by decide) (by decide) (List.drop 45 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data)) (left := 0) (count := 3421023) state57 gate58.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked58 :
    ∀ row ∈ (List.drop 45 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts58 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state58 : 3453636 ≤ oddCount 29029177 := by
  let row : Row := (58058353,58089031,3453637,6602)
  have hmem : row∈(List.drop 45 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data]; decide
  have h := (counts58 row hmem).2
  have slot : (row.1+1)/2 = 29029177 := by decide
  have value : row.2.2.1 = 3453637 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate59 : PLift (checkRows 29029177 676523 (composite primes 20 29029177 676523) 0 3453636 (List.take 43 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts59 :
    ∀ row ∈ (List.take 43 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 29029177) (width := 676523)
    (by decide) (by decide) (List.take 43 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data)) (left := 0) (count := 3453636) state58 gate59.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked59 :
    ∀ row ∈ (List.take 43 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts59 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state59 : 3529188 ≤ oddCount 29705700 := by
  let row : Row := (59411399,59446061,3529189,6611)
  have hmem : row∈(List.take 43 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data]; decide
  have h := (counts59 row hmem).2
  have slot : (row.1+1)/2 = 29705700 := by decide
  have value : row.2.2.1 = 3529189 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate60 : PLift (checkRows 29705700 323759 (composite primes 20 29705700 323759) 0 3529188 (List.drop 43 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts60 :
    ∀ row ∈ (List.drop 43 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 29705700) (width := 323759)
    (by decide) (by decide) (List.drop 43 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data)) (left := 0) (count := 3529188) state59 gate60.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked60 :
    ∀ row ∈ (List.drop 43 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts60 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state60 : 3565380 ≤ oddCount 30029459 := by
  let row : Row := (60058917,60094418,3565381,6615)
  have hmem : row∈(List.drop 43 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data]; decide
  have h := (counts60 row hmem).2
  have slot : (row.1+1)/2 = 30029459 := by decide
  have value : row.2.2.1 = 3565381 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate61 : PLift (checkRows 30029459 676063 (composite primes 20 30029459 676063) 0 3565380 (List.take 42 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts61 :
    ∀ row ∈ (List.take 42 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 30029459) (width := 676063)
    (by decide) (by decide) (List.take 42 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data)) (left := 0) (count := 3565380) state60 gate61.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked61 :
    ∀ row ∈ (List.take 42 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts61 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state61 : 3640806 ≤ oddCount 30705522 := by
  let row : Row := (61411044,61444830,3640807,6623)
  have hmem : row∈(List.take 42 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data]; decide
  have h := (counts61 row hmem).2
  have slot : (row.1+1)/2 = 30705522 := by decide
  have value : row.2.2.1 = 3640807 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate62 : PLift (checkRows 30705522 335986 (composite primes 20 30705522 335986) 0 3640806 (List.drop 42 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts62 :
    ∀ row ∈ (List.drop 42 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 30705522) (width := 335986)
    (by decide) (by decide) (List.drop 42 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data)) (left := 0) (count := 3640806) state61 gate62.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked62 :
    ∀ row ∈ (List.drop 42 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts62 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state62 : 3678244 ≤ oddCount 31041508 := by
  let row : Row := (62083015,62116621,3678245,6627)
  have hmem : row∈(List.drop 42 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data]; decide
  have h := (counts62 row hmem).2
  have slot : (row.1+1)/2 = 31041508 := by decide
  have value : row.2.2.1 = 3678245 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate63 : PLift (checkRows 31041508 686119 (composite primes 20 31041508 686119) 0 3678244 (List.take 44 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts63 :
    ∀ row ∈ (List.take 44 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 31041508) (width := 686119)
    (by decide) (by decide) (List.take 44 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data)) (left := 0) (count := 3678244) state62 gate63.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked63 :
    ∀ row ∈ (List.take 44 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts63 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state63 : 3754691 ≤ oddCount 31727627 := by
  let row : Row := (63455254,63489207,3754692,6635)
  have hmem : row∈(List.take 44 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data]; decide
  have h := (counts63 row hmem).2
  have slot : (row.1+1)/2 = 31727627 := by decide
  have value : row.2.2.1 = 3754692 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate64 : PLift (checkRows 31727627 322256 (composite primes 20 31727627 322256) 0 3754691 (List.drop 44 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts64 :
    ∀ row ∈ (List.drop 44 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 31727627) (width := 322256)
    (by decide) (by decide) (List.drop 44 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data)) (left := 0) (count := 3754691) state63 gate64.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked64 :
    ∀ row ∈ (List.drop 44 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts64 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state64 : 3790630 ≤ oddCount 32049883 := by
  let row : Row := (64099765,64138091,3790631,6639)
  have hmem : row∈(List.drop 44 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data]; decide
  have h := (counts64 row hmem).2
  have slot : (row.1+1)/2 = 32049883 := by decide
  have value : row.2.2.1 = 3790631 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate65 : PLift (checkRows 32049883 675780 (composite primes 20 32049883 675780) 0 3790630 (List.take 41 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts65 :
    ∀ row ∈ (List.take 41 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 32049883) (width := 675780)
    (by decide) (by decide) (List.take 41 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data)) (left := 0) (count := 3790630) state64 gate65.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked65 :
    ∀ row ∈ (List.take 41 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts65 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state65 : 3865629 ≤ oddCount 32725663 := by
  let row : Row := (65451326,65480579,3865630,6646)
  have hmem : row∈(List.take 41 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data]; decide
  have h := (counts65 row hmem).2
  have slot : (row.1+1)/2 = 32725663 := by decide
  have value : row.2.2.1 = 3865630 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate66 : PLift (checkRows 32725663 367312 (composite primes 20 32725663 367312) 0 3865629 (List.drop 41 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts66 :
    ∀ row ∈ (List.drop 41 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 32725663) (width := 367312)
    (by decide) (by decide) (List.drop 41 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data)) (left := 0) (count := 3865629) state65 gate66.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked66 :
    ∀ row ∈ (List.drop 41 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts66 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state66 : 3906499 ≤ oddCount 33092975 := by
  let row : Row := (66185950,66215323,3906500,6650)
  have hmem : row∈(List.drop 41 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data]; decide
  have h := (counts66 row hmem).2
  have slot : (row.1+1)/2 = 33092975 := by decide
  have value : row.2.2.1 = 3906500 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate67 : PLift (checkRows 33092975 671827 (composite primes 20 33092975 671827) 0 3906499 (List.take 38 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts67 :
    ∀ row ∈ (List.take 38 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 33092975) (width := 671827)
    (by decide) (by decide) (List.take 38 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data)) (left := 0) (count := 3906499) state66 gate67.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked67 :
    ∀ row ∈ (List.take 38 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts67 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state67 : 3981229 ≤ oddCount 33764802 := by
  let row : Row := (67529604,67568502,3981230,6658)
  have hmem : row∈(List.take 38 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data]; decide
  have h := (counts67 row hmem).2
  have slot : (row.1+1)/2 = 33764802 := by decide
  have value : row.2.2.1 = 3981230 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate68 : PLift (checkRows 33764802 480262 (composite primes 20 33764802 480262) 0 3981229 (List.drop 38 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts68 :
    ∀ row ∈ (List.drop 38 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 33764802) (width := 480262)
    (by decide) (by decide) (List.drop 38 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data)) (left := 0) (count := 3981229) state67 gate68.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked68 :
    ∀ row ∈ (List.drop 38 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts68 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state68 : 4034484 ≤ oddCount 34245064 := by
  let row : Row := (68490127,68527120,4034485,6663)
  have hmem : row∈(List.drop 38 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data]; decide
  have h := (counts68 row hmem).2
  have slot : (row.1+1)/2 = 34245064 := by decide
  have value : row.2.2.1 = 4034485 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate69 : PLift (checkRows 34245064 674777 (composite primes 20 34245064 674777) 0 4034484 (List.take 37 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts69 :
    ∀ row ∈ (List.take 37 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 34245064) (width := 674777)
    (by decide) (by decide) (List.take 37 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data)) (left := 0) (count := 4034484) state68 gate69.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked69 :
    ∀ row ∈ (List.take 37 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts69 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state69 : 4109274 ≤ oddCount 34919841 := by
  let row : Row := (69839682,69875577,4109275,6670)
  have hmem : row∈(List.take 37 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data]; decide
  have h := (counts69 row hmem).2
  have slot : (row.1+1)/2 = 34919841 := by decide
  have value : row.2.2.1 = 4109275 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate70 : PLift (checkRows 34919841 506108 (composite primes 20 34919841 506108) 0 4109274 (List.drop 37 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts70 :
    ∀ row ∈ (List.drop 37 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 34919841) (width := 506108)
    (by decide) (by decide) (List.drop 37 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data)) (left := 0) (count := 4109274) state69 gate70.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked70 :
    ∀ row ∈ (List.drop 37 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts70 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state70 : 4165169 ≤ oddCount 35425949 := by
  let row : Row := (70851897,70893909,4165170,6676)
  have hmem : row∈(List.drop 37 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data]; decide
  have h := (counts70 row hmem).2
  have slot : (row.1+1)/2 = 35425949 := by decide
  have value : row.2.2.1 = 4165170 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate71 : PLift (checkRows 35425949 678938 (composite primes 20 35425949 678938) 0 4165169 (List.take 36 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts71 :
    ∀ row ∈ (List.take 36 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 35425949) (width := 678938)
    (by decide) (by decide) (List.take 36 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data)) (left := 0) (count := 4165169) state70 gate71.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked71 :
    ∀ row ∈ (List.take 36 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts71 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state71 : 4240384 ≤ oddCount 36104887 := by
  let row : Row := (72209773,72254732,4240385,6683)
  have hmem : row∈(List.take 36 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data]; decide
  have h := (counts71 row hmem).2
  have slot : (row.1+1)/2 = 36104887 := by decide
  have value : row.2.2.1 = 4240385 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate72 : PLift (checkRows 36104887 561546 (composite primes 20 36104887 561546) 0 4240384 (List.drop 36 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts72 :
    ∀ row ∈ (List.drop 36 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 36104887) (width := 561546)
    (by decide) (by decide) (List.drop 36 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data)) (left := 0) (count := 4240384) state71 gate72.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked72 :
    ∀ row ∈ (List.drop 36 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts72 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state72 : 4302401 ≤ oddCount 36666433 := by
  let row : Row := (73332866,73369904,4302402,6688)
  have hmem : row∈(List.drop 36 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data]; decide
  have h := (counts72 row hmem).2
  have slot : (row.1+1)/2 = 36666433 := by decide
  have value : row.2.2.1 = 4302402 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate73 : PLift (checkRows 36666433 672276 (composite primes 20 36666433 672276) 0 4302401 (List.take 34 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts73 :
    ∀ row ∈ (List.take 34 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 36666433) (width := 672276)
    (by decide) (by decide) (List.take 34 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data)) (left := 0) (count := 4302401) state72 gate73.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked73 :
    ∀ row ∈ (List.take 34 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts73 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state73 : 4376470 ≤ oddCount 37338709 := by
  let row : Row := (74677418,74716222,4376471,6695)
  have hmem : row∈(List.take 34 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data]; decide
  have h := (counts73 row hmem).2
  have slot : (row.1+1)/2 = 37338709 := by decide
  have value : row.2.2.1 = 4376471 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate74 : PLift (checkRows 37338709 597092 (composite primes 20 37338709 597092) 0 4376470 (List.drop 34 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts74 :
    ∀ row ∈ (List.drop 34 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 37338709) (width := 597092)
    (by decide) (by decide) (List.drop 34 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data)) (left := 0) (count := 4376470) state73 gate74.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked74 :
    ∀ row ∈ (List.drop 34 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts74 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state74 : 4442481 ≤ oddCount 37935801 := by
  let row : Row := (75871601,75915569,4442482,6701)
  have hmem : row∈(List.drop 34 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data]; decide
  have h := (counts74 row hmem).2
  have slot : (row.1+1)/2 = 37935801 := by decide
  have value : row.2.2.1 = 4442482 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate75 : PLift (checkRows 37935801 676100 (composite primes 20 37935801 676100) 0 4442481 (List.take 33 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts75 :
    ∀ row ∈ (List.take 33 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 37935801) (width := 676100)
    (by decide) (by decide) (List.take 33 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data)) (left := 0) (count := 4442481) state74 gate75.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked75 :
    ∀ row ∈ (List.take 33 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts75 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state75 : 4516900 ≤ oddCount 38611901 := by
  let row : Row := (77223802,77260884,4516901,6707)
  have hmem : row∈(List.take 33 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data]; decide
  have h := (counts75 row hmem).2
  have slot : (row.1+1)/2 = 38611901 := by decide
  have value : row.2.2.1 = 4516901 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate76 : PLift (checkRows 38611901 629817 (composite primes 20 38611901 629817) 0 4516900 (List.drop 33 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts76 :
    ∀ row ∈ (List.drop 33 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 38611901) (width := 629817)
    (by decide) (by decide) (List.drop 33 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data)) (left := 0) (count := 4516900) state75 gate76.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked76 :
    ∀ row ∈ (List.drop 33 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts76 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state76 : 4586019 ≤ oddCount 39241718 := by
  let row : Row := (78483436,78517883,4586020,6713)
  have hmem : row∈(List.drop 33 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data]; decide
  have h := (counts76 row hmem).2
  have slot : (row.1+1)/2 = 39241718 := by decide
  have value : row.2.2.1 = 4586020 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate77 : PLift (checkRows 39241718 676291 (composite primes 20 39241718 676291) 0 4586019 (List.take 35 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts77 :
    ∀ row ∈ (List.take 35 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 39241718) (width := 676291)
    (by decide) (by decide) (List.take 35 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data)) (left := 0) (count := 4586019) state76 gate77.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked77 :
    ∀ row ∈ (List.take 35 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts77 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state77 : 4660391 ≤ oddCount 39918009 := by
  let row : Row := (79836018,79879812,4660392,6720)
  have hmem : row∈(List.take 35 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data]; decide
  have h := (counts77 row hmem).2
  have slot : (row.1+1)/2 = 39918009 := by decide
  have value : row.2.2.1 = 4660392 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate78 : PLift (checkRows 39918009 576196 (composite primes 20 39918009 576196) 0 4660391 (List.drop 35 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts78 :
    ∀ row ∈ (List.drop 35 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 39918009) (width := 576196)
    (by decide) (by decide) (List.drop 35 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data)) (left := 0) (count := 4660391) state77 gate78.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked78 :
    ∀ row ∈ (List.drop 35 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts78 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state78 : 4723778 ≤ oddCount 40494205 := by
  let row : Row := (80988410,81030419,4723779,6725)
  have hmem : row∈(List.drop 35 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data]; decide
  have h := (counts78 row hmem).2
  have slot : (row.1+1)/2 = 40494205 := by decide
  have value : row.2.2.1 = 4723779 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate79 : PLift (checkRows 40494205 688412 (composite primes 20 40494205 688412) 0 4723778 (List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts79 :
    ∀ row ∈ (List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 40494205) (width := 688412)
    (by decide) (by decide) (List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data)) (left := 0) (count := 4723778) state78 gate79.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked79 :
    ∀ row ∈ (List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts79 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state79 : 4799392 ≤ oddCount 41182617 := by
  let row : Row := (82365233,82405685,4799393,6731)
  have hmem : row∈(List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data]; decide
  have h := (counts79 row hmem).2
  have slot : (row.1+1)/2 = 41182617 := by decide
  have value : row.2.2.1 = 4799393 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate80 : PLift (checkRows 41182617 669932 (composite primes 20 41182617 669932) 0 4799392 (List.take 31 (List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data))) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts80 :
    ∀ row ∈ (List.take 31 (List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data))), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 41182617) (width := 669932)
    (by decide) (by decide) (List.take 31 (List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data))) (left := 0) (count := 4799392) state79 gate80.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked80 :
    ∀ row ∈ (List.take 31 (List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data))), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts80 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state80 : 4872791 ≤ oddCount 41852549 := by
  let row : Row := (83705098,83745347,4872792,6737)
  have hmem : row∈(List.take 31 (List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data))) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data]; decide
  have h := (counts80 row hmem).2
  have slot : (row.1+1)/2 = 41852549 := by decide
  have value : row.2.2.1 = 4872792 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate81 : PLift (checkRows 41852549 20125 (composite primes 20 41852549 20125) 0 4872791 (List.drop 63 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts81 :
    ∀ row ∈ (List.drop 63 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 41852549) (width := 20125)
    (by decide) (by decide) (List.drop 63 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data)) (left := 0) (count := 4872791) state80 gate81.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked81 :
    ∀ row ∈ (List.drop 63 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts81 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state81 : 4875031 ≤ oddCount 41872674 := by
  let row : Row := (83745348,83783844,4875032,6737)
  have hmem : row∈(List.drop 63 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data]; decide
  have h := (counts81 row hmem).2
  have slot : (row.1+1)/2 = 41872674 := by decide
  have value : row.2.2.1 = 4875032 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate82 : PLift (checkRows 41872674 683989 (composite primes 20 41872674 683989) 0 4875031 (List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts82 :
    ∀ row ∈ (List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 41872674) (width := 683989)
    (by decide) (by decide) (List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data)) (left := 0) (count := 4875031) state81 gate82.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked82 :
    ∀ row ∈ (List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts82 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state82 : 4949875 ≤ oddCount 42556663 := by
  let row : Row := (85113326,85150792,4949876,6743)
  have hmem : row∈(List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data]; decide
  have h := (counts82 row hmem).2
  have slot : (row.1+1)/2 = 42556663 := by decide
  have value : row.2.2.1 = 4949876 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate83 : PLift (checkRows 42556663 666613 (composite primes 20 42556663 666613) 0 4949875 (List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts83 :
    ∀ row ∈ (List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 42556663) (width := 666613)
    (by decide) (by decide) (List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data)) (left := 0) (count := 4949875) state82 gate83.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked83 :
    ∀ row ∈ (List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts83 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state83 : 5022905 ≤ oddCount 43223276 := by
  let row : Row := (86446552,86488944,5022906,6749)
  have hmem : row∈(List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data]; decide
  have h := (counts83 row hmem).2
  have slot : (row.1+1)/2 = 43223276 := by decide
  have value : row.2.2.1 = 5022906 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate84 : PLift (checkRows 43223276 681457 (composite primes 20 43223276 681457) 0 5022905 (List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts84 :
    ∀ row ∈ (List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 43223276) (width := 681457)
    (by decide) (by decide) (List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data)) (left := 0) (count := 5022905) state83 gate84.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked84 :
    ∀ row ∈ (List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts84 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state84 : 5097362 ≤ oddCount 43904733 := by
  let row : Row := (87809466,87854070,5097363,6755)
  have hmem : row∈(List.take 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data]; decide
  have h := (counts84 row hmem).2
  have slot : (row.1+1)/2 = 43904733 := by decide
  have value : row.2.2.1 = 5097363 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate85 : PLift (checkRows 43904733 687637 (composite primes 20 43904733 687637) 0 5097362 (List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data)) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts85 :
    ∀ row ∈ (List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data)), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 43904733) (width := 687637)
    (by decide) (by decide) (List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data)) (left := 0) (count := 5097362) state84 gate85.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked85 :
    ∀ row ∈ (List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data)), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts85 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state85 : 5172655 ≤ oddCount 44592370 := by
  let row : Row := (89184740,89236044,5172656,6761)
  have hmem : row∈(List.drop 32 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data)) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data]; decide
  have h := (counts85 row hmem).2
  have slot : (row.1+1)/2 = 44592370 := by decide
  have value : row.2.2.1 = 5172656 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate86 : PLift (checkRows 44592370 391985 (composite primes 20 44592370 391985) 0 5172655 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk103_data) = true) :=
  ⟨by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk103_data]; decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts86 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk103_data), 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts complete (markDepth := 20) (base := 44592370) (width := 391985)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk103_data) (left := 0) (count := 5172655) state85 gate86.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked86 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk103_data), row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := counts86 row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state86 : 5215225 ≤ oddCount 44984355 := by
  let row : Row := (89968710,89999999,5215226,6764)
  have hmem : row∈(Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk103_data) := by rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk103_data]; decide
  have h := (counts86 row hmem).2
  have slot : (row.1+1)/2 = 44984355 := by decide
  have value : row.2.2.1 = 5215226 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk070 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk070_data), row.2.2.1 ≤ row.1.primeCounting :=
  (checked28)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk071 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk071_data), row.2.2.1 ≤ row.1.primeCounting :=
  (checked29)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk072 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk072_data), row.2.2.1 ≤ row.1.primeCounting :=
  (checked30)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk073 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk073_data), row.2.2.1 ≤ row.1.primeCounting :=
  (checked31)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk074 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk074_data), row.2.2.1 ≤ row.1.primeCounting :=
  (checked32)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk075 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk075_data), row.2.2.1 ≤ row.1.primeCounting :=
  (checked33)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk076 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk076_data), row.2.2.1 ≤ row.1.primeCounting :=
  (checked34)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk077 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk077_data), row.2.2.1 ≤ row.1.primeCounting :=
  (checked35)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk078 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk078_data), row.2.2.1 ≤ row.1.primeCounting :=
  (checked36)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk079 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk079_data) 0 57 (checked37) ((checked38))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk080 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk080_data) 0 58 (checked39) ((checked40))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk081 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk081_data) 0 59 (checked41) ((checked42))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk082 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk082_data) 0 57 (checked43) ((checked44))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk083 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk083_data) 0 51 (checked45) ((checked46))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk084 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk084_data) 0 52 (checked47) ((checked48))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk085 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk085_data) 0 52 (checked49) ((checked50))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk086 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk086_data) 0 48 (checked51) ((checked52))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk087 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk087_data) 0 47 (checked53) ((checked54))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk088 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk088_data) 0 49 (checked55) ((checked56))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk089 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk089_data) 0 45 (checked57) ((checked58))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk090 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk090_data) 0 43 (checked59) ((checked60))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk091 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk091_data) 0 42 (checked61) ((checked62))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk092 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk092_data) 0 44 (checked63) ((checked64))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk093 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk093_data) 0 41 (checked65) ((checked66))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk094 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk094_data) 0 38 (checked67) ((checked68))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk095 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk095_data) 0 37 (checked69) ((checked70))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk096 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk096_data) 0 36 (checked71) ((checked72))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk097 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk097_data) 0 34 (checked73) ((checked74))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk098 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk098_data) 0 33 (checked75) ((checked76))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk099 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk099_data) 0 35 (checked77) ((checked78))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk100 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data) 0 32 (checked79) (joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk100_data) 32 31 (checked80) ((checked81)))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk101 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk101_data) 0 32 (checked82) ((checked83))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk102 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data), row.2.2.1 ≤ row.1.primeCounting :=
  joinRows (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk102_data) 0 32 (checked84) ((checked85))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem chunk103 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk103_data), row.2.2.1 ≤ row.1.primeCounting :=
  (checked86)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
theorem completeUpper : OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.H3 := by
  unfold OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.H3
  rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.upperRows_data]
  exact List.forall_mem_append.mpr ⟨chunk070,List.forall_mem_append.mpr ⟨chunk071,List.forall_mem_append.mpr ⟨chunk072,List.forall_mem_append.mpr ⟨chunk073,List.forall_mem_append.mpr ⟨chunk074,List.forall_mem_append.mpr ⟨chunk075,List.forall_mem_append.mpr ⟨chunk076,List.forall_mem_append.mpr ⟨chunk077,List.forall_mem_append.mpr ⟨chunk078,List.forall_mem_append.mpr ⟨chunk079,List.forall_mem_append.mpr ⟨chunk080,List.forall_mem_append.mpr ⟨chunk081,List.forall_mem_append.mpr ⟨chunk082,List.forall_mem_append.mpr ⟨chunk083,List.forall_mem_append.mpr ⟨chunk084,List.forall_mem_append.mpr ⟨chunk085,List.forall_mem_append.mpr ⟨chunk086,List.forall_mem_append.mpr ⟨chunk087,List.forall_mem_append.mpr ⟨chunk088,List.forall_mem_append.mpr ⟨chunk089,List.forall_mem_append.mpr ⟨chunk090,List.forall_mem_append.mpr ⟨chunk091,List.forall_mem_append.mpr ⟨chunk092,List.forall_mem_append.mpr ⟨chunk093,List.forall_mem_append.mpr ⟨chunk094,List.forall_mem_append.mpr ⟨chunk095,List.forall_mem_append.mpr ⟨chunk096,List.forall_mem_append.mpr ⟨chunk097,List.forall_mem_append.mpr ⟨chunk098,List.forall_mem_append.mpr ⟨chunk099,List.forall_mem_append.mpr ⟨chunk100,List.forall_mem_append.mpr ⟨chunk101,List.forall_mem_append.mpr ⟨chunk102,(chunk103)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end OMA.UpperPrimeCheckpoint

theorem OMA.solution : OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.H3 :=
  OMA.UpperPrimeCheckpoint.completeUpper