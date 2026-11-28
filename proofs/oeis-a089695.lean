import OMAStatements.S_oeis_a089695

namespace Magnanimous

/-- Interpret a decimal digit block from left to right, allowing leading zeros. -/
def value (w : List ℕ) : ℕ := Nat.ofDigits 10 w.reverse

/-- Every partition into consecutive nonempty digit blocks has a prime sum.
The one-block partition retains the original number. -/
def admissible (w : List ℕ) : Prop :=
  ∀ bs : List (List ℕ), bs.flatten = w → (∀ c ∈ bs, c ≠ []) → ((bs.map value).sum).Prime

end Magnanimous

/-! # An executable certificate for the decimal split-prime numbers

A state records the sum of the finished blocks and the value of the unfinished
last block of a prefix. If a digit is appended, the boundary before it is
either cut or left uncut.
-/

namespace Magnanimous

abbrev PrefixState := ℕ × ℕ

def extendStates (states : List PrefixState) (d : ℕ) : List PrefixState :=
  states.flatMap fun (s,b) => [(s+b,d), (s,10*b+d)]

private def trialDivisors : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]

/-- A necessary primality test, evaluated using only small divisors. -/
def mayPrime (n : ℕ) : Bool :=
  decide (2≤n) && trialDivisors.all fun d => n==d || n%d != 0

theorem mayPrime_of_prime {n : ℕ} (h : n.Prime) : mayPrime n=true := by
  have hgt : ∀ d ∈ trialDivisors, 1<d := by decide +kernel
  simp only [mayPrime,h.two_le,decide_true,Bool.true_and,List.all_eq_true]
  intro d hd
  by_cases he : n=d
  · simp [he]
  · have hmod : n%d≠0 := by
      intro hm
      rcases (Nat.dvd_prime h).mp (Nat.dvd_of_mod_eq_zero hm) with hh|hh
      · have := hgt d hd
        omega
      · exact he hh.symm
    simp [hmod]

/-- If the prefix can be extended at all, every current last block can
incorporate the next digit, leaving all subsequent digits as singletons.
The sum of those blocks is independent of the choice of next digit. -/
def canExtend (remaining : ℕ) (states : List PrefixState) : Bool :=
  states.all fun (s,b) => mayPrime (s + 10*b + remaining)

def searchPrefix (allowed : List ℕ) (fuel remaining n : ℕ)
    (states : List PrefixState) : Bool :=
  (remaining != 0 || allowed.contains n) &&
  (!canExtend remaining states ||
    match fuel with
    | 0 => false
    | k+1 => (List.range (min 9 remaining+1)).all fun d =>
        searchPrefix allowed k (remaining-d) (10*n+d) (extendStates states d))
termination_by fuel

/-- Verify all words with the specified sum and a positive leading digit. -/
def prefixCheck (allowed : List ℕ) (fuel S : ℕ) : Bool :=
  !mayPrime S || (List.range (min 9 S)).all fun i =>
    searchPrefix allowed fuel (S-(i+1)) (i+1) [(0,i+1)]

end Magnanimous

/-! # Soundness of the finite prefix certificate -/

namespace Magnanimous

private def represents (w : List ℕ) (s b : ℕ) : Prop :=
  ∃ (blocks : List (List ℕ)) (last : List ℕ),
    blocks.flatten++last=w ∧ (∀ c∈blocks, c≠[]) ∧ last≠[] ∧
    (blocks.map value).sum=s ∧ value last=b

private def validStates (w : List ℕ) (states : List PrefixState) : Prop :=
  ∀ t ∈ states, represents w t.1 t.2

private theorem value_append_digit (w : List ℕ) (d : ℕ) :
    value (w++[d]) = 10*value w+d := by simp [value,Nat.ofDigits,Nat.add_comm]

private theorem valid_initial (d : ℕ) : validStates [d] [(0,d)] := by
  intro t ht
  obtain rfl : t=(0,d) := by simpa using ht
  exact ⟨[],[d],rfl,by simp,by simp,rfl,by simp [value]⟩

private theorem valid_extend {w : List ℕ} {states : List PrefixState}
    (hv : validStates w states) (d : ℕ) : validStates (w++[d]) (extendStates states d) := by
  intro t ht
  obtain ⟨⟨s,b⟩,hs,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨bs,l,hf,hn,hp,hv,hl⟩ := hv _ hs
  change t ∈ [(s+b,d),(s,10*b+d)] at ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl
  · refine ⟨bs++[l],[d],?_,?_,by simp,?_,by simp [value]⟩
    · simp [hf]
    · intro c hc
      rcases List.mem_append.mp hc with hm|hm
      · exact hn _ hm
      · obtain rfl : c=l := by simpa using hm
        exact hp
    · simp [hv,hl]
  · exact ⟨bs,l++[d],by simpa [List.append_assoc] using congrArg (·++[d]) hf,
      hn,by simp,hv,by rw [value_append_digit,hl]⟩

private theorem flatten_singles (ds : List ℕ) : (ds.map (fun i => [i])).flatten=ds := by
  induction ds <;> simp_all

private theorem singleton_prime {w : List ℕ} (h : admissible w) : w.sum.Prime := by
  let bs := w.map fun d => [d]
  have hf : bs.flatten=w := flatten_singles w
  have hn : ∀ c∈bs,c≠[] := by simp [bs]
  simpa [bs,List.map_map,Function.comp_def,value] using h bs hf hn

private theorem extend_required {w tail : List ℕ} {d : ℕ} {states : List PrefixState}
    (h : admissible (w++d::tail)) (hv : validStates w states) :
    canExtend (d+tail.sum) states=true := by
  apply List.all_eq_true.mpr
  rintro ⟨s,b⟩ ht
  obtain ⟨bs,l,hf,hn,hl,hs,hb⟩ := hv _ ht
  let singles := tail.map fun i => [i]
  have hsf : singles.flatten=tail := flatten_singles tail
  have hsp : ∀ c∈singles,c≠[] := by simp [singles]
  have hss : (singles.map value).sum=tail.sum := by
    simp [singles,List.map_map,Function.comp_def,value]
  let joined := bs++(l++[d])::singles
  have hjoin : joined.flatten=w++d::tail := by
    simp [joined,hsf,←hf,List.append_assoc]
  have hjn : ∀ c∈joined,c≠[] := by
    intro c hc
    rcases List.mem_append.mp hc with hleft|hright
    · exact hn _ hleft
    · rcases List.mem_cons.mp hright with rfl|hr
      · simp
      · exact hsp _ hr
  have hp := h joined hjoin hjn
  apply mayPrime_of_prime
  simpa [joined,hs,hss,value_append_digit,hb,Nat.add_assoc] using hp

private theorem search_sound {allowed : List ℕ} (tail : List ℕ) :
    ∀ (w : List ℕ) (states : List PrefixState) (fuel : ℕ),
    admissible (w++tail) → (∀ x ∈ tail, x<10) → validStates w states →
    searchPrefix allowed fuel tail.sum (value w) states = true →
    value (w++tail) ∈ allowed := by
  induction tail with
  | nil =>
    intro w states fuel _ _ _ hc
    rw [searchPrefix.eq_def] at hc
    simpa using (Bool.and_eq_true_iff.mp hc).1
  | cons d tail ih =>
    intro w states fuel h hd hv hc
    have he := extend_required h hv
    rw [searchPrefix.eq_def] at hc
    have hbranch := (Bool.and_eq_true_iff.mp hc).2
    simp only [List.sum_cons,he,Bool.not_true,Bool.false_or] at hbranch
    cases fuel with
    | zero => contradiction
    | succ fuel =>
      have hlt := hd d (by simp)
      have hdmem : d ∈ List.range (min 9 (d+tail.sum)+1) := List.mem_range.mpr (by omega)
      have child := List.all_eq_true.mp hbranch d hdmem
      have hds : d+tail.sum-d=tail.sum := by omega
      have hc' : searchPrefix allowed fuel tail.sum (value (w++[d])) (extendStates states d)=true := by
        simpa only [value_append_digit,hds] using child
      have h' : admissible ((w++[d])++tail) := by simpa [List.append_assoc] using h
      have hdt : ∀ x ∈ tail, x<10 := fun x hx => hd x (by simp [hx])
      simpa [List.append_assoc] using ih (w++[d]) (extendStates states d) fuel h' hdt (valid_extend hv _) hc'

/-- A successful certificate includes the value of every admissible canonical word. -/
theorem prefixCheck_sound {allowed : List ℕ} {d : ℕ} {ds : List ℕ} {fuel : ℕ}
    (hd : 0<d) (hsmall : ∀ x∈d::ds, x<10) (h : admissible (d::ds))
    (hc : prefixCheck allowed fuel (d::ds).sum=true) : value (d::ds) ∈ allowed := by
  have hp := singleton_prime h
  simp only [prefixCheck,mayPrime_of_prime hp,Bool.not_true,Bool.false_or] at hc
  have hd9 := hsmall d (by simp)
  have hmem : d-1∈List.range (min 9 (d::ds).sum) := by simp; omega
  have hs := List.all_eq_true.mp hc (d-1) hmem
  rw [show d-1+1=d by omega] at hs
  have hchild : searchPrefix allowed fuel ds.sum (value [d]) [(0,d)]=true := by
    simpa [value] using hs
  exact search_sound ds [d] [(0,d)] fuel (by simpa using h)
    (fun x hx => hsmall x (by simp [hx])) (valid_initial d) hchild

end Magnanimous

/-! # Bounding the number of nonzero digits

Joining two adjacent digits d,e changes the singleton sum by 9d.
Greedily take disjoint pairs beginning at each occurrence of one fixed digit.
-/

namespace Magnanimous

private def capacity (d : ℕ) : List ℕ → ℕ
  | [] | [_] => 0
  | x :: y :: xs => if x=d then capacity d xs+1 else capacity d (y::xs)

private theorem count_capacity (d : ℕ) :
    ∀ w : List ℕ, w.count d ≤ 2*capacity d w+1
  | [] => by simp [capacity]
  | [x] => by by_cases hx : x=d <;> simp [capacity,hx]
  | x :: y :: xs => by
    by_cases hx : x=d
    · have ih := count_capacity d xs
      by_cases hy : y=d <;> simp [capacity,hx,hy] <;> omega
    · have ih := count_capacity d (y::xs)
      simpa only [capacity,if_neg hx,List.count_cons,beq_eq_false_iff_ne.mpr hx,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using ih

private def HasSum (w : List ℕ) (s : ℕ) : Prop :=
  ∃ bs : List (List ℕ), bs.flatten=w ∧ (∀ c ∈ bs, c ≠ []) ∧ (bs.map value).sum=s

private theorem singleton_sum (w : List ℕ) : HasSum w w.sum := by
  refine ⟨w.map fun x => [x], ?_, ?_, ?_⟩
  · induction w <;> simp_all
  · simp
  · simp [List.map_map, Function.comp_def,value]

private theorem prepend_block {w : List ℕ} {s : ℕ} (h : HasSum w s)
    (c : List ℕ) (hc : c≠[]) : HasSum (c++w) (value c+s) := by
  obtain ⟨bs,hf,hne,hs⟩ := h
  exact ⟨c::bs, by simp [hf], by simpa [hc] using hne, by simp [hs]⟩

private theorem realizable (d : ℕ) :
    ∀ (w : List ℕ) (j : ℕ), j ≤ capacity d w → HasSum w (w.sum+9*d*j)
  | [], j, hj => by
    have : j=0 := by simpa [capacity] using hj
    simpa [this] using singleton_sum []
  | [x], j, hj => by
    have : j=0 := by simpa [capacity] using hj
    simpa [this] using singleton_sum [x]
  | x::y::xs, j, hj => by
    by_cases hx : x=d
    · subst x
      cases j with
      | zero => simpa using singleton_sum (d::y::xs)
      | succ j =>
        have hj' : j ≤ capacity d xs := by simpa [capacity] using hj
        have he := prepend_block (realizable d xs j hj') [d,y] (by simp)
        convert he using 1 <;> simp [value,Nat.ofDigits] <;> try ring
    · have hj' : j ≤ capacity d (y::xs) := by simpa [capacity,hx] using hj
      have he := prepend_block (realizable d (y::xs) j hj') [x] (by simp)
      simpa [value,Nat.ofDigits,Nat.add_assoc] using he

private theorem count_le_sum (d : ℕ) (hd : 0<d) (w : List ℕ) : w.count d ≤ w.sum := by
  induction w with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : x=d <;> simp [hx] <;> omega

private theorem modular_choice :
    ∀ d : Fin 10, d.val ≠ 0 → ∀ s : Fin 11,
      ∃ j : Fin 11, (s.val+9*d.val*j.val)%11=0 := by decide +kernel

private theorem digit_count_le {w : List ℕ} (h : admissible w)
    {d : ℕ} (hpos : 0<d) (hsmall : d<10) : w.count d ≤ 21 := by
  by_contra! hmany
  have hc := count_capacity d w
  have hs := count_le_sum d hpos w
  obtain ⟨j,hj⟩ := modular_choice ⟨d,hsmall⟩ hpos.ne' ⟨w.sum%11,Nat.mod_lt _ (by decide)⟩
  change (w.sum%11+9*d*j.val)%11=0 at hj
  have hdiv : 11 ∣ w.sum+9*d*j.val := Nat.dvd_of_mod_eq_zero (by
    simpa only [Nat.mod_add_mod] using hj)
  obtain ⟨bs,hf,hne,hval⟩ := realizable d w j.val (by have := j.isLt; omega)
  have hp := h bs hf hne
  rw [hval] at hp
  rcases (Nat.dvd_prime hp).mp hdiv with hbad|heq <;> omega

private theorem sum_counts (w : List ℕ) (hd : ∀ a∈w, a<10) :
    (w.filter (· != 0)).length =
      w.count 1+w.count 2+w.count 3+w.count 4+w.count 5+
      w.count 6+w.count 7+w.count 8+w.count 9 := by
  induction w with
  | nil => simp
  | cons x xs ih =>
    have hx : x<10 := hd x (by simp)
    have hxs := ih (by intro a ha; exact hd _ (by simp [ha]))
    interval_cases x <;> simp <;> omega

theorem nonzero_le {w : List ℕ} (h : admissible w) (hd : ∀ a∈w, a<10) :
    (w.filter (· != 0)).length ≤ 199 := by
  rw [sum_counts w hd]
  have H1 := digit_count_le h (by decide : 0<1) (by decide)
  have H2 := digit_count_le h (by decide : 0<2) (by decide)
  have H3 := digit_count_le h (by decide : 0<3) (by decide)
  have H4 := digit_count_le h (by decide : 0<4) (by decide)
  have H5 := digit_count_le h (by decide : 0<5) (by decide)
  have H6 := digit_count_le h (by decide : 0<6) (by decide)
  have H7 := digit_count_le h (by decide : 0<7) (by decide)
  have H8 := digit_count_le h (by decide : 0<8) (by decide)
  have H9 := digit_count_le h (by decide : 0<9) (by decide)
  omega

end Magnanimous

namespace Magnanimous

/-- The admissible positive decimal numerals in ascending order. -/
def terms : List ℕ :=
  [2, 3, 5, 7, 11, 23, 29, 41, 43, 47, 61, 67, 83, 89, 101, 227, 229, 281, 401,
   443, 449, 467, 601, 607, 647, 661, 683, 809, 821, 863, 881, 4001, 4463, 4643,
   6007, 6067, 6803, 8009]

private def checkBlock (i : ℕ) : Bool :=
  (List.range 64).all (fun j => prefixCheck terms 8 (i * 64 + j))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows00 : checkBlock 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows01 : checkBlock 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows02 : checkBlock 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows03 : checkBlock 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows04 : checkBlock 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows05 : checkBlock 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows06 : checkBlock 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows07 : checkBlock 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows08 : checkBlock 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows09 : checkBlock 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows10 : checkBlock 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows11 : checkBlock 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows12 : checkBlock 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows13 : checkBlock 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows14 : checkBlock 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows15 : checkBlock 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows16 : checkBlock 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows17 : checkBlock 17 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows18 : checkBlock 18 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows19 : checkBlock 19 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows20 : checkBlock 20 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows21 : checkBlock 21 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows22 : checkBlock 22 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows23 : checkBlock 23 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows24 : checkBlock 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows25 : checkBlock 25 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows26 : checkBlock 26 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows27 : checkBlock 27 = true := by decide +kernel

private theorem checked_block {i : ℕ} (hi : i < 28) : checkBlock i = true := by
  interval_cases i
  · exact rows00
  · exact rows01
  · exact rows02
  · exact rows03
  · exact rows04
  · exact rows05
  · exact rows06
  · exact rows07
  · exact rows08
  · exact rows09
  · exact rows10
  · exact rows11
  · exact rows12
  · exact rows13
  · exact rows14
  · exact rows15
  · exact rows16
  · exact rows17
  · exact rows18
  · exact rows19
  · exact rows20
  · exact rows21
  · exact rows22
  · exact rows23
  · exact rows24
  · exact rows25
  · exact rows26
  · exact rows27

/-- The prefix search accepts exactly the permitted terminal numerals and
exhausts every branch for each possible digit sum. -/
theorem checked_prefixes {S : ℕ} (h : S ≤ 1791) : prefixCheck terms 8 S = true := by
  have hblock : S / 64 < 28 := by omega
  have hb := checked_block hblock
  unfold checkBlock at hb
  have hm : S % 64 ∈ List.range 64 := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have hresult := List.all_eq_true.mp hb (S % 64) hm
  change prefixCheck terms 8 (S / 64 * 64 + S % 64) = true at hresult
  have he : S / 64 * 64 + S % 64 = S := by omega
  simpa only [he] using hresult

theorem terms_length : terms.length = 38 := by decide

end Magnanimous

namespace Magnanimous

/-- Prepend the digit as a singleton, or join it to the first existing block. -/
private def prependCut (a : ℕ) (bs : List (List ℕ)) : List (List (List ℕ)) :=
  ([a] :: bs) :: match bs with
    | [] => []
    | c :: cs => [(a :: c) :: cs]

private def allCuts : List ℕ → List (List (List ℕ))
  | [] => [[]]
  | a :: w => (allCuts w).flatMap (prependCut a)

private theorem mem_allCuts {w : List ℕ} {bs : List (List ℕ)} (hf : bs.flatten = w)
    (hn : ∀ b ∈ bs, b ≠ []) : bs ∈ allCuts w := by
  induction w generalizing bs with
  | nil =>
    cases bs with
    | nil => simp [allCuts]
    | cons b bs =>
      have hb := hn b (by simp)
      simp only [List.flatten_cons, List.append_eq_nil_iff] at hf
      exact (hb hf.1).elim
  | cons a w ih =>
    cases bs with
    | nil => simp at hf
    | cons b bs =>
      have hb := hn b (by simp)
      have hs : ∀ c ∈ bs, c ≠ [] := fun c hc => hn c (by simp [hc])
      cases b with
      | nil => exact (hb rfl).elim
      | cons b rest =>
        simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hf
        obtain ⟨rfl, hrest⟩ := hf
        apply List.mem_flatMap.mpr
        cases rest with
        | nil =>
          refine ⟨bs, ih (by simpa using hrest) hs, ?_⟩
          simp [prependCut]
        | cons d ds =>
          have htail : ∀ c ∈ (d :: ds) :: bs, c ≠ [] := by
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact List.cons_ne_nil _ _
            · exact hs c hc
          refine ⟨(d :: ds) :: bs, ih (by simpa using hrest) htail, ?_⟩
          simp [prependCut]

/-- Test every sum against a list of certified primes. -/
def allCutsListed (primes w : List ℕ) : Bool :=
  (allCuts w).all fun bs => primes.contains (bs.map value).sum

theorem admissible_of_allCutsListed {primes w : List ℕ}
    (hp : ∀ p ∈ primes, p.Prime) (h : allCutsListed primes w = true) : admissible w := by
  intro bs hf hn
  exact hp _ (by simpa using List.all_eq_true.mp h bs (mem_allCuts hf hn))

end Magnanimous

namespace Magnanimous

private def partitionPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 43, 47, 53, 61, 67, 71, 73, 83, 89,
   101, 107, 127, 227, 229, 281, 401, 443, 449, 467, 601, 607, 613, 647, 661, 683,
   809, 821, 863, 881, 4001, 4463, 4643, 6007, 6067, 6803, 8009]

private theorem partitionPrimes_prime (p : ℕ) (h : p ∈ partitionPrimes) : p.Prime := by
  simp only [partitionPrimes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

set_option maxRecDepth 100000 in
private theorem terms_pass :
    terms.all (fun n => decide (0 < n) &&
      allCutsListed partitionPrimes (Nat.digits 10 n).reverse) = true := by
  decide +kernel

/-- Every entry passes the prime test for every nonempty-block decomposition of
its usual decimal word, including the decomposition with a single block. -/
theorem admissible_of_mem_terms {n : ℕ} (hn : n ∈ terms) :
    0 < n ∧ admissible (Nat.digits 10 n).reverse := by
  have ht := List.all_eq_true.mp terms_pass n hn
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  exact ⟨ht.1, admissible_of_allCutsListed partitionPrimes_prime ht.2⟩

end Magnanimous

/-! # Complete classification of decimal split-prime numbers (OEIS A089695) -/

namespace Magnanimous

private theorem sum_le_nine_nonzero (w : List ℕ) (hd : ∀ x∈w, x<10) :
    w.sum ≤ 9*(w.filter (· != 0)).length := by
  induction w with
  | nil => simp
  | cons d ds ih =>
    have hd' := hd d (by simp)
    have hs := ih (by intro x hx; exact hd x (by simp [hx]))
    by_cases hz : d=0 <;> simp [hz] <;> omega

/-- The 38 terms in the OEIS table give the complete sequence. -/
theorem classification (n : ℕ) :
    (0<n ∧ admissible (Nat.digits 10 n).reverse) ↔ n∈terms := by
  refine ⟨?_,admissible_of_mem_terms⟩
  rintro ⟨hn,ha⟩
  let w := (Nat.digits 10 n).reverse
  have hv : value w=n := by simp [value,w,Nat.ofDigits_digits]
  have hd : ∀ d∈w, d<10 := fun d h => Nat.digits_lt_base (by decide) (List.mem_reverse.mp h)
  have hf : w.head? ≠ some 0 := by
    dsimp [w]
    rw [List.head?_reverse,List.getLast?_eq_some_getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne')]
    exact fun h => Nat.getLast_digit_ne_zero 10 hn.ne' (Option.some.inj h)
  have hs := sum_le_nine_nonzero w hd
  have hct := nonzero_le (w:=w) ha hd
  have hbound : w.sum≤1791 := by omega
  change admissible w at ha
  have hc := checked_prefixes hbound
  rw [←hv]
  cases he : w with
  | nil =>
    rw [he] at hv
    have : 0=n := by simpa [value] using hv
    omega
  | cons d ds =>
    rw [he] at hf ha hd hc
    have hz : d ≠ 0 := by simpa using hf
    exact prefixCheck_sound (Nat.pos_of_ne_zero hz) hd ha hc

theorem largest_term : IsGreatest {n : ℕ | 0<n ∧ admissible (Nat.digits 10 n).reverse} 8009 := by
  refine ⟨(classification _).mpr (by decide +kernel),?_⟩
  have hmax : ∀ n ∈ terms, n ≤ 8009 := by decide +kernel
  exact fun n hn => hmax _ ((classification n).mp hn)

theorem number_of_terms : {n : ℕ | 0<n ∧ admissible (Nat.digits 10 n).reverse}.ncard=38 := by
  have he : {n : ℕ | 0<n ∧ admissible (Nat.digits 10 n).reverse} = (↑terms.toFinset : Set ℕ) := by
    ext n
    simpa using classification n
  rw [he, Set.ncard_coe_finset]
  decide +kernel

end Magnanimous

theorem OMA.solution : type_of% @OMA.S_oeis_a089695.main := by
  apply (Set.finite_Iic (8009 : ℕ)).subset
  exact fun _ hn => Magnanimous.largest_term.2 hn
