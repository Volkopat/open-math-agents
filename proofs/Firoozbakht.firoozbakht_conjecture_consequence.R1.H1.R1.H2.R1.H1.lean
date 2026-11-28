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

/-! Trial division for the primes that mark odd composite slots. -/
namespace OMA.PrimeRoster

private def checks (q : ℕ) : Bool :=
  decide (3≤q ∧ q%2=1) &&
  (List.range' 3 49).all (fun k => decide (q≤k ∨ q%k≠0))

def smallPrimes (bound : ℕ) : List ℕ :=
  (List.range (bound+1)).filter checks

theorem mem_smallPrimes {q bound : ℕ} (hq : q≤bound) (prime : q.Prime) (odd : q%2=1) :
    q ∈ smallPrimes bound := by
  unfold smallPrimes checks
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨by omega, ⟨by have := prime.two_le; omega,odd⟩, ?_⟩
  intro k hk
  have lower : 3≤k := (List.mem_range'_1.mp hk).1
  by_cases h : q≤k
  · exact Or.inl h
  · right
    intro zero
    exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero zero) (by omega) (by omega) prime

theorem prime_of_mem_smallPrimes {q bound : ℕ} (boundSmall : bound≤2702)
    (member : q ∈ smallPrimes bound) : q.Prime := by
  unfold smallPrimes checks at member
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at member
  obtain ⟨within,⟨large,odd⟩,all⟩ := member
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
  have psmall : p≤51 := by
    by_contra! ht
    have hpow : 52^2≤p^2 := Nat.pow_le_pow_left ht 2
    have hl := Nat.minFac_sq_le_self (by omega : 0<q) hn
    change p^2≤q at hl
    omega
  have lt : p<q := (Nat.not_prime_iff_minFac_lt (by omega : 2≤q)).mp hn
  have hb : p ∈ List.range' 3 49 := List.mem_range'_1.mpr ⟨plarge,by omega⟩
  exact (all p hb).elim (fun h => (Nat.not_le_of_lt lt) h) (fun h => h (Nat.mod_eq_zero_of_dvd dvd))

end OMA.PrimeRoster

open OMA.PrimePopulation OMA.PrimeProgression

private def basePrimes : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def rosterEquality : PLift (OMA.PrimeRoster.smallPrimes 2702 = basePrimes) :=
  ⟨by decide +kernel⟩

private theorem baseComplete : ∀ p ≤ 2702, p.Prime → p%2=1 → p∈basePrimes := by
  intro p hp prime odd
  rw [← rosterEquality.down]
  exact OMA.PrimeRoster.mem_smallPrimes hp prime odd

private theorem bounds_from_counts {rows : List Row}
    (h : ∀ row ∈ rows, 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2)) :
    ∀ row ∈ rows, row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have hrow := h row hr
  exact hrow.2.trans (oddCount_le_primeCounting hrow.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem dispatchLower
    (check00 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk000_data), row.2.2.1 ≤ row.1.primeCounting)
    (check01 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk001_data), row.2.2.1 ≤ row.1.primeCounting)
    (check02 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk002_data), row.2.2.1 ≤ row.1.primeCounting)
    (check03 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk003_data), row.2.2.1 ≤ row.1.primeCounting)
    (check04 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk004_data), row.2.2.1 ≤ row.1.primeCounting)
    (check05 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk005_data), row.2.2.1 ≤ row.1.primeCounting)
    (check06 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk006_data), row.2.2.1 ≤ row.1.primeCounting)
    (check07 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk007_data), row.2.2.1 ≤ row.1.primeCounting)
    (check08 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk008_data), row.2.2.1 ≤ row.1.primeCounting)
    (check09 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk009_data), row.2.2.1 ≤ row.1.primeCounting)
    (check10 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk010_data), row.2.2.1 ≤ row.1.primeCounting)
    (check11 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk011_data), row.2.2.1 ≤ row.1.primeCounting)
    (check12 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk012_data), row.2.2.1 ≤ row.1.primeCounting)
    (check13 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk013_data), row.2.2.1 ≤ row.1.primeCounting)
    (check14 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk014_data), row.2.2.1 ≤ row.1.primeCounting)
    (check15 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk015_data), row.2.2.1 ≤ row.1.primeCounting)
    (check16 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk016_data), row.2.2.1 ≤ row.1.primeCounting)
    (check17 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk017_data), row.2.2.1 ≤ row.1.primeCounting)
    (check18 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk018_data), row.2.2.1 ≤ row.1.primeCounting)
    (check19 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk019_data), row.2.2.1 ≤ row.1.primeCounting)
    (check20 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk020_data), row.2.2.1 ≤ row.1.primeCounting)
    (check21 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk021_data), row.2.2.1 ≤ row.1.primeCounting)
    (check22 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk022_data), row.2.2.1 ≤ row.1.primeCounting)
    (check23 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk023_data), row.2.2.1 ≤ row.1.primeCounting)
    (check24 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk024_data), row.2.2.1 ≤ row.1.primeCounting)
    (check25 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk025_data), row.2.2.1 ≤ row.1.primeCounting)
    (check26 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk026_data), row.2.2.1 ≤ row.1.primeCounting)
    (check27 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk027_data), row.2.2.1 ≤ row.1.primeCounting)
    (check28 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk028_data), row.2.2.1 ≤ row.1.primeCounting)
    (check29 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk029_data), row.2.2.1 ≤ row.1.primeCounting)
    (check30 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk030_data), row.2.2.1 ≤ row.1.primeCounting)
    (check31 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk031_data), row.2.2.1 ≤ row.1.primeCounting)
    (check32 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk032_data), row.2.2.1 ≤ row.1.primeCounting)
    (check33 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk033_data), row.2.2.1 ≤ row.1.primeCounting)
    (check34 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk034_data), row.2.2.1 ≤ row.1.primeCounting) : OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.H1 := by
  unfold OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.H1
  rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.lowerRows_data]
  exact List.forall_mem_append.mpr ⟨check00,List.forall_mem_append.mpr ⟨check01,List.forall_mem_append.mpr ⟨check02,List.forall_mem_append.mpr ⟨check03,List.forall_mem_append.mpr ⟨check04,List.forall_mem_append.mpr ⟨check05,List.forall_mem_append.mpr ⟨check06,List.forall_mem_append.mpr ⟨check07,List.forall_mem_append.mpr ⟨check08,List.forall_mem_append.mpr ⟨check09,List.forall_mem_append.mpr ⟨check10,List.forall_mem_append.mpr ⟨check11,List.forall_mem_append.mpr ⟨check12,List.forall_mem_append.mpr ⟨check13,List.forall_mem_append.mpr ⟨check14,List.forall_mem_append.mpr ⟨check15,List.forall_mem_append.mpr ⟨check16,List.forall_mem_append.mpr ⟨check17,List.forall_mem_append.mpr ⟨check18,List.forall_mem_append.mpr ⟨check19,List.forall_mem_append.mpr ⟨check20,List.forall_mem_append.mpr ⟨check21,List.forall_mem_append.mpr ⟨check22,List.forall_mem_append.mpr ⟨check23,List.forall_mem_append.mpr ⟨check24,List.forall_mem_append.mpr ⟨check25,List.forall_mem_append.mpr ⟨check26,List.forall_mem_append.mpr ⟨check27,List.forall_mem_append.mpr ⟨check28,List.forall_mem_append.mpr ⟨check29,List.forall_mem_append.mpr ⟨check30,List.forall_mem_append.mpr ⟨check31,List.forall_mem_append.mpr ⟨check32,List.forall_mem_append.mpr ⟨check33,check34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate00 : PLift (checkedSegment basePrimes 18 11 0 65536 = 12250) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state00 : 12250 ≤ oddCount 65536 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 0) (width := 65536) (current := 0) (by decide) (by decide) (by decide) (Nat.zero_le (oddCount 0))
  rw [gate00.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate01 : PLift (checkedSegment basePrimes 18 11 65536 65536 = 10749) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state01 : 22999 ≤ oddCount 131072 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 65536) (width := 65536) (current := 12250) (by decide) (by decide) (by decide) state00
  rw [gate01.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate02 : PLift (checkedSegment basePrimes 18 11 131072 65536 = 10335) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state02 : 33334 ≤ oddCount 196608 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 131072) (width := 65536) (current := 22999) (by decide) (by decide) (by decide) state01
  rw [gate02.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate03 : PLift (checkedSegment basePrimes 18 11 196608 65536 = 10055) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state03 : 43389 ≤ oddCount 262144 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 196608) (width := 65536) (current := 33334) (by decide) (by decide) (by decide) state02
  rw [gate03.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate04 : PLift (checkedSegment basePrimes 18 11 262144 65536 = 9838) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state04 : 53227 ≤ oddCount 327680 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 262144) (width := 65536) (current := 43389) (by decide) (by decide) (by decide) state03
  rw [gate04.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate05 : PLift (checkedSegment basePrimes 18 11 327680 65536 = 9718) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state05 : 62945 ≤ oddCount 393216 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 327680) (width := 65536) (current := 53227) (by decide) (by decide) (by decide) state04
  rw [gate05.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate06 : PLift (checkedSegment basePrimes 18 11 393216 65536 = 9601) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state06 : 72546 ≤ oddCount 458752 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 393216) (width := 65536) (current := 62945) (by decide) (by decide) (by decide) state05
  rw [gate06.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate07 : PLift (checkedSegment basePrimes 18 11 458752 65536 = 9478) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state07 : 82024 ≤ oddCount 524288 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 458752) (width := 65536) (current := 72546) (by decide) (by decide) (by decide) state06
  rw [gate07.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate08 : PLift (checkedSegment basePrimes 18 11 524288 65536 = 9440) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state08 : 91464 ≤ oddCount 589824 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 524288) (width := 65536) (current := 82024) (by decide) (by decide) (by decide) state07
  rw [gate08.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate09 : PLift (checkedSegment basePrimes 18 11 589824 65536 = 9321) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state09 : 100785 ≤ oddCount 655360 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 589824) (width := 65536) (current := 91464) (by decide) (by decide) (by decide) state08
  rw [gate09.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate10 : PLift (checkedSegment basePrimes 18 11 655360 65536 = 9270) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state10 : 110055 ≤ oddCount 720896 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 655360) (width := 65536) (current := 100785) (by decide) (by decide) (by decide) state09
  rw [gate10.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate11 : PLift (checkedSegment basePrimes 18 11 720896 65536 = 9212) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state11 : 119267 ≤ oddCount 786432 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 720896) (width := 65536) (current := 110055) (by decide) (by decide) (by decide) state10
  rw [gate11.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate12 : PLift (checkedSegment basePrimes 18 11 786432 65536 = 9145) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state12 : 128412 ≤ oddCount 851968 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 786432) (width := 65536) (current := 119267) (by decide) (by decide) (by decide) state11
  rw [gate12.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate13 : PLift (checkedSegment basePrimes 18 11 851968 34132 = 4701) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state13 : 133113 ≤ oddCount 886100 := by
  have h := checkedSegment_add baseComplete (markDepth := 18) (popDepth := 11)
    (base := 851968) (width := 34132) (current := 128412) (by decide) (by decide) (by decide) state12
  rw [gate13.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate14 : PLift (checkRows 886100 23326 (composite basePrimes 18 886100 23326) 0 133113 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk000_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk000_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts00 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk000_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 886100) (width := 23326)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk000_data) (left := 0) (count := 133113) state13 gate14.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked00 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk000_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts00

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state14 : 136373 ≤ oddCount 909426 := by
  let row : Row := (1818852, 1819665, 136374, 5323)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk000_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk000_data]
    decide
  have h := (counts00 row mem).2
  have slot : (row.1+1)/2 = 909426 := by decide
  have value : row.2.2.1 = 136374 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate15 : PLift (checkRows 909426 31947 (composite basePrimes 18 909426 31947) 0 136373 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk001_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk001_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts01 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk001_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 909426) (width := 31947)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk001_data) (left := 0) (count := 136373) state14 gate15.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked01 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk001_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts01

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state15 : 140836 ≤ oddCount 941373 := by
  let row : Row := (1882745, 1884197, 140837, 5336)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk001_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk001_data]
    decide
  have h := (counts01 row mem).2
  have slot : (row.1+1)/2 = 941373 := by decide
  have value : row.2.2.1 = 140837 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate16 : PLift (checkRows 941373 45915 (composite basePrimes 18 941373 45915) 0 140836 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk002_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk002_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts02 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk002_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 941373) (width := 45915)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk002_data) (left := 0) (count := 140836) state15 gate16.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked02 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk002_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts02

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state16 : 147157 ≤ oddCount 987288 := by
  let row : Row := (1974576, 1975569, 147158, 5353)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk002_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk002_data]
    decide
  have h := (counts02 row mem).2
  have slot : (row.1+1)/2 = 987288 := by decide
  have value : row.2.2.1 = 147158 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate17 : PLift (checkRows 987288 47075 (composite basePrimes 18 987288 47075) 0 147157 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk003_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk003_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts03 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk003_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 987288) (width := 47075)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk003_data) (left := 0) (count := 147157) state16 gate17.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked03 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk003_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts03

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state17 : 153676 ≤ oddCount 1034363 := by
  let row : Row := (2068725, 2070192, 153677, 5370)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk003_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk003_data]
    decide
  have h := (counts03 row mem).2
  have slot : (row.1+1)/2 = 1034363 := by decide
  have value : row.2.2.1 = 153677 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate18 : PLift (checkRows 1034363 51059 (composite basePrimes 18 1034363 51059) 0 153676 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk004_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk004_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts04 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk004_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1034363) (width := 51059)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk004_data) (left := 0) (count := 153676) state17 gate18.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked04 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk004_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts04

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state18 : 160690 ≤ oddCount 1085422 := by
  let row : Row := (2170844, 2172547, 160691, 5388)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk004_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk004_data]
    decide
  have h := (counts04 row mem).2
  have slot : (row.1+1)/2 = 1085422 := by decide
  have value : row.2.2.1 = 160691 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate19 : PLift (checkRows 1085422 51344 (composite basePrimes 18 1085422 51344) 0 160690 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk005_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk005_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts05 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk005_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1085422) (width := 51344)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk005_data) (left := 0) (count := 160690) state18 gate19.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked05 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk005_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts05

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state19 : 167729 ≤ oddCount 1136766 := by
  let row : Row := (2273532, 2275471, 167730, 5405)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk005_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk005_data]
    decide
  have h := (counts05 row mem).2
  have slot : (row.1+1)/2 = 1136766 := by decide
  have value : row.2.2.1 = 167730 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate20 : PLift (checkRows 1136766 48689 (composite basePrimes 18 1136766 48689) 0 167729 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk006_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk006_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts06 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk006_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1136766) (width := 48689)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk006_data) (left := 0) (count := 167729) state19 gate20.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked06 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk006_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts06

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state20 : 174313 ≤ oddCount 1185455 := by
  let row : Row := (2370909, 2372378, 174314, 5421)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk006_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk006_data]
    decide
  have h := (counts06 row mem).2
  have slot : (row.1+1)/2 = 1185455 := by decide
  have value : row.2.2.1 = 174314 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate21 : PLift (checkRows 1185455 40926 (composite basePrimes 18 1185455 40926) 0 174313 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk007_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk007_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts07 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk007_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1185455) (width := 40926)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk007_data) (left := 0) (count := 174313) state20 gate21.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked07 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk007_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts07

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state21 : 179873 ≤ oddCount 1226381 := by
  let row : Row := (2452761, 2453920, 179874, 5433)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk007_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk007_data]
    decide
  have h := (counts07 row mem).2
  have slot : (row.1+1)/2 = 1226381 := by decide
  have value : row.2.2.1 = 179874 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate22 : PLift (checkRows 1226381 40055 (composite basePrimes 18 1226381 40055) 0 179873 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk008_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk008_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts08 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk008_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1226381) (width := 40055)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk008_data) (left := 0) (count := 179873) state21 gate22.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked08 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk008_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts08

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state22 : 185322 ≤ oddCount 1266436 := by
  let row : Row := (2532872, 2534307, 185323, 5445)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk008_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk008_data]
    decide
  have h := (counts08 row mem).2
  have slot : (row.1+1)/2 = 1266436 := by decide
  have value : row.2.2.1 = 185323 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate23 : PLift (checkRows 1266436 45051 (composite basePrimes 18 1266436 45051) 0 185322 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk009_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk009_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts09 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk009_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1266436) (width := 45051)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk009_data) (left := 0) (count := 185322) state22 gate23.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked09 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk009_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts09

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state23 : 191411 ≤ oddCount 1311487 := by
  let row : Row := (2622973, 2624343, 191412, 5458)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk009_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk009_data]
    decide
  have h := (counts09 row mem).2
  have slot : (row.1+1)/2 = 1311487 := by decide
  have value : row.2.2.1 = 191412 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate24 : PLift (checkRows 1311487 55181 (composite basePrimes 18 1311487 55181) 0 191411 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk010_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk010_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts10 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk010_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1311487) (width := 55181)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk010_data) (left := 0) (count := 191411) state23 gate24.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked10 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk010_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts10

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state24 : 198889 ≤ oddCount 1366668 := by
  let row : Row := (2733335, 2734984, 198890, 5473)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk010_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk010_data]
    decide
  have h := (counts10 row mem).2
  have slot : (row.1+1)/2 = 1366668 := by decide
  have value : row.2.2.1 = 198890 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate25 : PLift (checkRows 1366668 55106 (composite basePrimes 18 1366668 55106) 0 198889 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk011_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk011_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts11 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk011_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1366668) (width := 55106)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk011_data) (left := 0) (count := 198889) state24 gate25.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked11 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk011_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts11

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state25 : 206357 ≤ oddCount 1421774 := by
  let row : Row := (2843547, 2846098, 206358, 5488)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk011_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk011_data]
    decide
  have h := (counts11 row mem).2
  have slot : (row.1+1)/2 = 1421774 := by decide
  have value : row.2.2.1 = 206358 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate26 : PLift (checkRows 1421774 64643 (composite basePrimes 18 1421774 64643) 0 206357 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk012_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk012_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts12 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk012_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1421774) (width := 64643)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk012_data) (left := 0) (count := 206357) state25 gate26.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked12 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk012_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts12

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state26 : 214980 ≤ oddCount 1486417 := by
  let row : Row := (2972833, 2974382, 214981, 5504)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk012_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk012_data]
    decide
  have h := (counts12 row mem).2
  have slot : (row.1+1)/2 = 1486417 := by decide
  have value : row.2.2.1 = 214981 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate27 : PLift (checkRows 1486417 55104 (composite basePrimes 18 1486417 55104) 0 214980 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk013_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk013_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts13 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk013_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1486417) (width := 55104)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk013_data) (left := 0) (count := 214980) state26 gate27.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked13 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk013_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts13

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state27 : 222357 ≤ oddCount 1541521 := by
  let row : Row := (3083041, 3084913, 222358, 5518)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk013_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk013_data]
    decide
  have h := (counts13 row mem).2
  have slot : (row.1+1)/2 = 1541521 := by decide
  have value : row.2.2.1 = 222358 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate28 : PLift (checkRows 1541521 61790 (composite basePrimes 18 1541521 61790) 0 222357 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk014_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk014_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts14 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk014_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1541521) (width := 61790)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk014_data) (left := 0) (count := 222357) state27 gate28.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked14 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk014_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts14

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state28 : 230657 ≤ oddCount 1603311 := by
  let row : Row := (3206622, 3208847, 230658, 5532)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk014_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk014_data]
    decide
  have h := (counts14 row mem).2
  have slot : (row.1+1)/2 = 1603311 := by decide
  have value : row.2.2.1 = 230658 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate29 : PLift (checkRows 1603311 87384 (composite basePrimes 18 1603311 87384) 0 230657 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk015_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk015_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts15 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk015_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1603311) (width := 87384)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk015_data) (left := 0) (count := 230657) state28 gate29.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked15 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk015_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts15

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state29 : 242296 ≤ oddCount 1690695 := by
  let row : Row := (3381390, 3383945, 242297, 5552)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk015_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk015_data]
    decide
  have h := (counts15 row mem).2
  have slot : (row.1+1)/2 = 1690695 := by decide
  have value : row.2.2.1 = 242297 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate30 : PLift (checkRows 1690695 79589 (composite basePrimes 18 1690695 79589) 0 242296 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk016_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk016_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts16 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk016_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1690695) (width := 79589)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk016_data) (left := 0) (count := 242296) state29 gate30.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked16 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk016_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts16

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state30 : 252794 ≤ oddCount 1770284 := by
  let row : Row := (3540567, 3542248, 252795, 5569)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk016_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk016_data]
    decide
  have h := (counts16 row mem).2
  have slot : (row.1+1)/2 = 1770284 := by decide
  have value : row.2.2.1 = 252795 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate31 : PLift (checkRows 1770284 55118 (composite basePrimes 18 1770284 55118) 0 252794 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk017_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk017_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts17 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk017_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1770284) (width := 55118)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk017_data) (left := 0) (count := 252794) state30 gate31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked17 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk017_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts17

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state31 : 260119 ≤ oddCount 1825402 := by
  let row : Row := (3650803, 3652670, 260120, 5580)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk017_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk017_data]
    decide
  have h := (counts17 row mem).2
  have slot : (row.1+1)/2 = 1825402 := by decide
  have value : row.2.2.1 = 260120 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate32 : PLift (checkRows 1825402 72675 (composite basePrimes 18 1825402 72675) 0 260119 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk018_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk018_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts18 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk018_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1825402) (width := 72675)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk018_data) (left := 0) (count := 260119) state31 gate32.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked18 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk018_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts18

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state32 : 269717 ≤ oddCount 1898077 := by
  let row : Row := (3796154, 3798449, 269718, 5595)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk018_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk018_data]
    decide
  have h := (counts18 row mem).2
  have slot : (row.1+1)/2 = 1898077 := by decide
  have value : row.2.2.1 = 269718 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate33 : PLift (checkRows 1898077 83292 (composite basePrimes 18 1898077 83292) 0 269717 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk019_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk019_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts19 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk019_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1898077) (width := 83292)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk019_data) (left := 0) (count := 269717) state32 gate33.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked19 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk019_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts19

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state33 : 280735 ≤ oddCount 1981369 := by
  let row : Row := (3962738, 3965831, 280736, 5611)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk019_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk019_data]
    decide
  have h := (counts19 row mem).2
  have slot : (row.1+1)/2 = 1981369 := by decide
  have value : row.2.2.1 = 280736 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate34 : PLift (checkRows 1981369 84117 (composite basePrimes 18 1981369 84117) 0 280735 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk020_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk020_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts20 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk020_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 1981369) (width := 84117)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk020_data) (left := 0) (count := 280735) state33 gate34.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked20 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk020_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts20

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state34 : 291778 ≤ oddCount 2065486 := by
  let row : Row := (4130971, 4133732, 291779, 5626)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk020_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk020_data]
    decide
  have h := (counts20 row mem).2
  have slot : (row.1+1)/2 = 2065486 := by decide
  have value : row.2.2.1 = 291779 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate35 : PLift (checkRows 2065486 86059 (composite basePrimes 18 2065486 86059) 0 291778 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk021_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk021_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts21 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk021_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 2065486) (width := 86059)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk021_data) (left := 0) (count := 291778) state34 gate35.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked21 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk021_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts21

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state35 : 303031 ≤ oddCount 2151545 := by
  let row : Row := (4303089, 4305518, 303032, 5641)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk021_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk021_data]
    decide
  have h := (counts21 row mem).2
  have slot : (row.1+1)/2 = 2151545 := by decide
  have value : row.2.2.1 = 303032 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate36 : PLift (checkRows 2151545 70662 (composite basePrimes 18 2151545 70662) 0 303031 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk022_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk022_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts22 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk022_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 2151545) (width := 70662)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk022_data) (left := 0) (count := 303031) state35 gate36.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked22 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk022_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts22

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state36 : 312296 ≤ oddCount 2222207 := by
  let row : Row := (4444414, 4447346, 312297, 5653)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk022_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk022_data]
    decide
  have h := (counts22 row mem).2
  have slot : (row.1+1)/2 = 2222207 := by decide
  have value : row.2.2.1 = 312297 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate37 : PLift (checkRows 2222207 93746 (composite basePrimes 18 2222207 93746) 0 312296 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk023_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk023_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts23 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk023_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 2222207) (width := 93746)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk023_data) (left := 0) (count := 312296) state36 gate37.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked23 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk023_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts23

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state37 : 324529 ≤ oddCount 2315953 := by
  let row : Row := (4631906, 4634790, 324530, 5668)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk023_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk023_data]
    decide
  have h := (counts23 row mem).2
  have slot : (row.1+1)/2 = 2315953 := by decide
  have value : row.2.2.1 = 324530 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate38 : PLift (checkRows 2315953 94912 (composite basePrimes 18 2315953 94912) 0 324529 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk024_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk024_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts24 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk024_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 2315953) (width := 94912)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk024_data) (left := 0) (count := 324529) state37 gate38.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked24 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk024_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts24

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state38 : 336857 ≤ oddCount 2410865 := by
  let row : Row := (4821729, 4824592, 336858, 5683)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk024_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk024_data]
    decide
  have h := (counts24 row mem).2
  have slot : (row.1+1)/2 = 2410865 := by decide
  have value : row.2.2.1 = 336858 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate39 : PLift (checkRows 2410865 111080 (composite basePrimes 18 2410865 111080) 0 336857 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk025_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk025_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts25 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk025_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 2410865) (width := 111080)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk025_data) (left := 0) (count := 336857) state38 gate39.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked25 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk025_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts25

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state39 : 351340 ≤ oddCount 2521945 := by
  let row : Row := (5043889, 5048262, 351341, 5700)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk025_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk025_data]
    decide
  have h := (counts25 row mem).2
  have slot : (row.1+1)/2 = 2521945 := by decide
  have value : row.2.2.1 = 351341 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate40 : PLift (checkRows 2521945 124400 (composite basePrimes 18 2521945 124400) 0 351340 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk026_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk026_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts26 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk026_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 2521945) (width := 124400)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk026_data) (left := 0) (count := 351340) state39 gate40.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked26 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk026_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts26

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state40 : 367431 ≤ oddCount 2646345 := by
  let row : Row := (5292689, 5296450, 367432, 5717)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk026_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk026_data]
    decide
  have h := (counts26 row mem).2
  have slot : (row.1+1)/2 = 2646345 := by decide
  have value : row.2.2.1 = 367432 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate41 : PLift (checkRows 2646345 132194 (composite basePrimes 18 2646345 132194) 0 367431 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk027_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk027_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts27 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk027_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 2646345) (width := 132194)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk027_data) (left := 0) (count := 367431) state40 gate41.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked27 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk027_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts27

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state41 : 384421 ≤ oddCount 2778539 := by
  let row : Row := (5557077, 5560171, 384422, 5735)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk027_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk027_data]
    decide
  have h := (counts27 row mem).2
  have slot : (row.1+1)/2 = 2778539 := by decide
  have value : row.2.2.1 = 384422 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate42 : PLift (checkRows 2778539 110751 (composite basePrimes 18 2778539 110751) 0 384421 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk028_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk028_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts28 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk028_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 2778539) (width := 110751)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk028_data) (left := 0) (count := 384421) state41 gate42.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked28 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk028_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts28

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state42 : 398630 ≤ oddCount 2889290 := by
  let row : Row := (5778579, 5781943, 398631, 5750)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk028_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk028_data]
    decide
  have h := (counts28 row mem).2
  have slot : (row.1+1)/2 = 2889290 := by decide
  have value : row.2.2.1 = 398631 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate43 : PLift (checkRows 2889290 105977 (composite basePrimes 18 2889290 105977) 0 398630 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk029_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk029_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts29 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk029_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 2889290) (width := 105977)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk029_data) (left := 0) (count := 398630) state42 gate43.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked29 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk029_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts29

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state43 : 412257 ≤ oddCount 2995267 := by
  let row : Row := (5990533, 5994166, 412258, 5763)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk029_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk029_data]
    decide
  have h := (counts29 row mem).2
  have slot : (row.1+1)/2 = 2995267 := by decide
  have value : row.2.2.1 = 412258 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate44 : PLift (checkRows 2995267 116898 (composite basePrimes 18 2995267 116898) 0 412257 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk030_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk030_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts30 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk030_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 2995267) (width := 116898)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk030_data) (left := 0) (count := 412257) state43 gate44.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked30 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk030_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts30

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state44 : 427179 ≤ oddCount 3112165 := by
  let row : Row := (6224329, 6227389, 427180, 5777)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk030_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk030_data]
    decide
  have h := (counts30 row mem).2
  have slot : (row.1+1)/2 = 3112165 := by decide
  have value : row.2.2.1 = 427180 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate45 : PLift (checkRows 3112165 119565 (composite basePrimes 18 3112165 119565) 0 427179 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk031_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk031_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts31 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk031_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 3112165) (width := 119565)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk031_data) (left := 0) (count := 427179) state44 gate45.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked31 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk031_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts31

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state45 : 442432 ≤ oddCount 3231730 := by
  let row : Row := (6463459, 6466586, 442433, 5791)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk031_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk031_data]
    decide
  have h := (counts31 row mem).2
  have slot : (row.1+1)/2 = 3231730 := by decide
  have value : row.2.2.1 = 442433 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate46 : PLift (checkRows 3231730 115384 (composite basePrimes 18 3231730 115384) 0 442432 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk032_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk032_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts32 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk032_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 3231730) (width := 115384)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk032_data) (left := 0) (count := 442432) state45 gate46.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked32 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk032_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts32

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state46 : 457125 ≤ oddCount 3347114 := by
  let row : Row := (6694227, 6697494, 457126, 5804)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk032_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk032_data]
    decide
  have h := (counts32 row mem).2
  have slot : (row.1+1)/2 = 3347114 := by decide
  have value : row.2.2.1 = 457126 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate47 : PLift (checkRows 3347114 134568 (composite basePrimes 18 3347114 134568) 0 457125 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk033_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk033_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts33 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk033_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 3347114) (width := 134568)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk033_data) (left := 0) (count := 457125) state46 gate47.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked33 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk033_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts33

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state47 : 474324 ≤ oddCount 3481682 := by
  let row : Row := (6963363, 6968823, 474325, 5819)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk033_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk033_data]
    decide
  have h := (counts33 row mem).2
  have slot : (row.1+1)/2 = 3481682 := by decide
  have value : row.2.2.1 = 474325 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate48 : PLift (checkRows 3481682 169696 (composite basePrimes 18 3481682 169696) 0 474324 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk034_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk034_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts34 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk034_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 18) (base := 3481682) (width := 169696)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk034_data) (left := 0) (count := 474324) state47 gate48.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked34 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk034_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts34

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state48 : 495832 ≤ oddCount 3651378 := by
  let row : Row := (7302755, 7307735, 495833, 5836)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk034_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk034_data]
    decide
  have h := (counts34 row mem).2
  have slot : (row.1+1)/2 = 3651378 := by decide
  have value : row.2.2.1 = 495833 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.H1 :=
  dispatchLower checked00 checked01 checked02 checked03 checked04 checked05 checked06 checked07 checked08 checked09 checked10 checked11 checked12 checked13 checked14 checked15 checked16 checked17 checked18 checked19 checked20 checked21 checked22 checked23 checked24 checked25 checked26 checked27 checked28 checked29 checked30 checked31 checked32 checked33 checked34