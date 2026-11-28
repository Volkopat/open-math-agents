import OMAReductions.R_oeis_a389525_R1

namespace A389525Pilot

structure Masks where
  one : Nat := 0
  two : Nat := 0
  three : Nat := 0
  cover : Nat := 0

def step (mask : Nat) (w : Nat) (s : Masks) : Masks :=
  let one := s.one ||| (1 <<< w)
  let two := (s.two ||| (one <<< w)) &&& mask
  let three := (s.three ||| (two <<< w)) &&& mask
  let cover := (s.cover ||| (three <<< (2*w))) &&& mask
  ⟨one, two, three, cover⟩

def packed (upper : Nat) (values : List Nat) : Nat :=
  let mask := (1 <<< (upper+1)) - 1
  (values.foldr (step mask) {}).cover


/-- The bits at the first 2^l multiples of d, starting at zero. -/
def progression (d : Nat) : Nat → Nat
  | 0 => 1
  | l+1 =>
    let old := progression d l
    old ||| (old <<< (d * 2^l))

theorem progression_bit (d l n : Nat) :
    (progression d l).testBit n = true ↔ ∃ k < 2^l, n = d*k := by
  induction l generalizing n with
  | zero =>
    simp only [progression, Nat.testBit_one_eq_true_iff_self_eq_zero, pow_zero]
    constructor
    · intro hn
      exact ⟨0, Nat.zero_lt_one, by simpa using hn⟩
    · rintro ⟨k, hk, hn⟩
      simpa [show k = 0 by omega] using hn
  | succ l ih =>
    simp only [progression, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftLeft,
      Bool.and_eq_true, decide_eq_true_eq, ih, pow_succ]
    constructor
    · rintro (⟨k, hk, rfl⟩ | ⟨hle, k, hk, he⟩)
      · have hpos : 0 < (2:Nat)^l := Nat.two_pow_pos l
        exact ⟨k, by omega, rfl⟩
      · refine ⟨2^l+k, by omega, ?_⟩
        rw [Nat.mul_add]
        omega
    · rintro ⟨k, hk, rfl⟩
      by_cases hl : k < 2^l
      · exact Or.inl ⟨k, hl, rfl⟩
      · refine Or.inr ⟨Nat.mul_le_mul_left _ (by omega), k-2^l, by omega, ?_⟩
        exact (Nat.mul_sub_left_distrib _ _ _).symm

def marked (upper d : Nat) : Nat :=
  progression d ((upper / d).log2 + 1) <<< (d*d)

theorem marked_bit (upper d n : Nat) (hd : 0 < d) (hn : n ≤ upper) :
    (marked upper d).testBit n = true ↔ d*d ≤ n ∧ d ∣ n := by
  simp only [marked, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, progression_bit]
  constructor
  · rintro ⟨hle, k, _, he⟩
    refine ⟨hle, d+k, ?_⟩
    rw [Nat.mul_add]
    omega
  · rintro ⟨hle, k, rfl⟩
    have hdk : d ≤ k := Nat.le_of_mul_le_mul_left hle hd
    have hku : k ≤ upper/d := (Nat.le_div_iff_mul_le hd).mpr (by rwa [Nat.mul_comm])
    have hu := Nat.lt_log2_self (n := upper/d)
    exact ⟨hle, k-d, by omega, (Nat.mul_sub_left_distrib _ _ _).symm⟩

def compositeMask (upper : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds =>
    (if 2 ≤ d ∧ d.minFac = d then marked upper d else 0) ||| compositeMask upper ds

theorem compositeMask_bit (upper n : Nat) (hn : n ≤ upper) (ds : List Nat) :
    (compositeMask upper ds).testBit n = true ↔
      ∃ d ∈ ds, d.Prime ∧ d*d ≤ n ∧ d ∣ n := by
  induction ds with
  | nil => simp [compositeMask]
  | cons d ds ih =>
    simp only [compositeMask, Nat.testBit_or, Bool.or_eq_true, List.mem_cons, ih]
    by_cases hd : d.Prime
    · rw [if_pos (Nat.prime_def_minFac.mp hd), marked_bit upper d n hd.pos hn]
      constructor
      · rintro (⟨hle, hdvd⟩ | ⟨e, he, hp, hle, hdvd⟩)
        · exact ⟨d, Or.inl rfl, hd, hle, hdvd⟩
        · exact ⟨e, Or.inr he, hp, hle, hdvd⟩
      · rintro ⟨e, rfl | he, hp, hle, hdvd⟩
        · exact Or.inl ⟨hle, hdvd⟩
        · exact Or.inr ⟨e, he, hp, hle, hdvd⟩
    · rw [if_neg (fun h => hd (Nat.prime_def_minFac.mpr h))]
      simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
      constructor
      · rintro ⟨e, he, hp, hle, hdvd⟩
        exact ⟨e, Or.inr he, hp, hle, hdvd⟩
      · rintro ⟨e, rfl | he, hp, hle, hdvd⟩
        · exact (hd hp).elim
        · exact ⟨e, he, hp, hle, hdvd⟩

/-- Mark composites and the two naturals below the first prime. -/
def nonprimeMask (upper : Nat) : Nat :=
  compositeMask upper (List.range (upper.sqrt + 1)) ||| 3

theorem nonprimeMask_bit (upper n : Nat) (hn : n ≤ upper) :
    (nonprimeMask upper).testBit n = true ↔ ¬ n.Prime := by
  have hsmall : (3:Nat).testBit n = decide (n < 2) := Nat.testBit_two_pow_sub_one 2 n
  simp only [nonprimeMask, Nat.testBit_or, Bool.or_eq_true, compositeMask_bit upper n hn,
    List.mem_range, hsmall, decide_eq_true_eq]
  constructor
  · rintro (⟨d, _, hp, hsq, hdvd⟩ | hs) hp'
    · exact (Nat.prime_def_le_sqrt.mp hp').2 d hp.two_le (Nat.le_sqrt.mpr hsq) hdvd
    · have := hp'.two_le
      omega
  · intro hnp
    by_cases h2 : 2 ≤ n
    · have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
      have hsq : n.minFac * n.minFac ≤ n := by
        simpa only [pow_two] using Nat.minFac_sq_le_self (by omega : 0 < n) hnp
      have hle : n.minFac ≤ upper.sqrt := Nat.le_sqrt.mpr (hsq.trans hn)
      exact Or.inl ⟨n.minFac, by omega, hp, hsq, Nat.minFac_dvd n⟩
    · exact Or.inr (by omega)

def sieve (upper : Nat) : Nat := ((1 <<< (upper + 1)) - 1) ^^^ nonprimeMask upper

theorem sieve_bit (upper n : Nat) (hn : n ≤ upper) :
    (sieve upper).testBit n = true ↔ n.Prime := by
  have hlow : ((1 <<< (upper + 1)) - 1).testBit n = true := by
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (by omega)
  rw [sieve, Nat.testBit_xor, hlow]
  cases hb : (nonprimeMask upper).testBit n
  · have hp : n.Prime := by
      by_contra hnp
      have he := (nonprimeMask_bit upper n hn).mpr hnp
      rw [hb] at he
      contradiction
    simp [hp]
  · have hnp := (nonprimeMask_bit upper n hn).mp hb
    simp [hnp]

theorem count_congr_lt (p q : Nat → Prop) [DecidablePred p] [DecidablePred q]
    (n : Nat) (h : ∀ i < n, p i ↔ q i) : Nat.count p n = Nat.count q n := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (h i)

theorem cpopRec_count {w : Nat} (x : BitVec w) (n : Nat) :
    x.cpopNatRec n 0 = Nat.count (fun i => x.getLsbD i = true) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [BitVec.cpopNatRec_succ, BitVec.cpopNatRec_add, Nat.count_succ, ih]
    cases x.getLsbD n <;> simp

theorem cpop_count (m len : Nat) :
    (BitVec.ofNat len m).cpop.toNat = Nat.count (fun i => m.testBit i = true) len := by
  rw [BitVec.toNat_cpop, cpopRec_count]
  apply count_congr_lt
  intro i hi
  rw [BitVec.getLsbD_ofNat]
  simp [hi]

def trim (m size : Nat) : Nat := m &&& ((1 <<< size) - 1)

theorem trim_bit (m size i : Nat) (hi : i < size) :
    (trim m size).testBit i = m.testBit i := by
  have h : ((1 <<< size) - 1).testBit i = true := by
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hi
  rw [trim, Nat.testBit_and, h, Bool.and_true]

/-- Count the low len bits in balanced blocks so recursion depth stays bounded. -/
def rankBits (m len : Nat) : Nat :=
  if len ≤ 32 then (BitVec.ofNat len m).cpop.toNat
  else
    let half := len / 2
    rankBits (trim m half) half + rankBits (m >>> half) (len-half)
termination_by len
decreasing_by all_goals omega

theorem rankBits_eq (m len : Nat) :
    rankBits m len = Nat.count (fun i => m.testBit i = true) len := by
  by_cases h : len ≤ 32
  · rw [rankBits, if_pos h, cpop_count]
  · let l := len / 2
    let r := len-l
    have hlr : l+r = len := by dsimp [l, r]; omega
    have hl : Nat.count (fun i => (trim m l).testBit i = true) l =
        Nat.count (fun i => m.testBit i = true) l := by
      apply count_congr_lt
      intro i hi
      rw [trim_bit m l i hi]
    calc
      rankBits m len = rankBits (trim m l) l + rankBits (m >>> l) r := by
        rw [rankBits, if_neg h]
      _ = Nat.count (fun i => m.testBit i = true) l +
          Nat.count (fun i => m.testBit (l+i) = true) r := by
        rw [rankBits_eq (trim m l) l, rankBits_eq (m >>> l) r, hl]
        simp only [Nat.testBit_shiftRight]
      _ = Nat.count (fun i => m.testBit i = true) (l+r) := (Nat.count_add _ l r).symm
      _ = _ := by rw [hlr]
termination_by len
decreasing_by all_goals omega

theorem sieve_count (upper len : Nat) (h : len ≤ upper+1) :
    rankBits (sieve upper) len = Nat.count Nat.Prime len := by
  rw [rankBits_eq]
  apply count_congr_lt
  intro i hi
  exact sieve_bit upper i (by omega)

theorem verifiedRank (q k : Nat) (hq : q.Prime) (h : rankBits (sieve q) q = k - 1) :
    Nat.nth Nat.Prime (k-1) = q := by
  rw [sieve_count q q (by omega)] at h
  rw [← h]
  exact Nat.nth_count hq

theorem interval_prime_count (bound a q : Nat) (haq : a ≤ q) (hqb : q ≤ bound) :
    rankBits (sieve bound >>> a) (q-a) = Nat.count Nat.Prime q - Nat.count Nat.Prime a := by
  rw [rankBits_eq]
  have he : Nat.count (fun i => (sieve bound >>> a).testBit i = true) (q-a) =
      Nat.count (fun i => Nat.Prime (a+i)) (q-a) := by
    apply count_congr_lt
    intro i hi
    rw [Nat.testBit_shiftRight]
    exact sieve_bit bound (a+i) (by omega)
  rw [he]
  have h := Nat.count_add Nat.Prime a (q-a)
  rw [show a + (q-a) = q by omega] at h
  omega

def checkRanks (bound bits : Nat) (a i : Nat) : List Nat → Bool
  | [] => true
  | q :: qs =>
    decide (a ≤ q ∧ q ≤ bound) &&
      bits.testBit q &&
      decide (rankBits (bits >>> a) (q-a) = (i^2-1) - ((i-1)^2-1)) &&
      checkRanks bound bits q (i+1) qs

def IndexedWeights (i : Nat) : List Nat → Prop
  | [] => True
  | q :: qs => Nat.nth Nat.Prime (i^2-1) = q ∧ IndexedWeights (i+1) qs

theorem indexedWeights_of_check (bound a i : Nat) (qs : List Nat)
    (hcount : Nat.count Nat.Prime a = (i-1)^2-1)
    (h : checkRanks bound (sieve bound) a i qs = true) : IndexedWeights i qs := by
  induction qs generalizing a i with
  | nil => trivial
  | cons q qs ih =>
    simp only [checkRanks, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨haq, hqb⟩, hq⟩, hr⟩, hrest⟩ := h
    have hp := (sieve_bit bound q hqb).mp hq
    have hmono := Nat.count_monotone Nat.Prime haq
    have hpow : (i-1)^2 ≤ i^2 := Nat.pow_le_pow_left (by omega) 2
    have hqcount : Nat.count Nat.Prime q = i^2-1 := by
      rw [interval_prime_count bound a q haq hqb] at hr
      omega
    refine ⟨?_, ih q (i+1) (by simpa only [Nat.add_sub_cancel] using hqcount) hrest⟩
    rw [← hqcount]
    exact Nat.nth_count hp

noncomputable def weight (i : Nat) : Nat := Nat.nth Nat.Prime (i^2-1)

def RepOne (a n : Nat) : Prop := ∃ i, a ≤ i ∧ n = weight i

def RepTwo (a n : Nat) : Prop :=
  ∃ i j, a ≤ j ∧ j ≤ i ∧ n = weight i + weight j

def RepThree (a n : Nat) : Prop :=
  ∃ i j k, a ≤ k ∧ k ≤ j ∧ j ≤ i ∧ n = weight i + weight j + weight k

def RepFour (a n : Nat) : Prop :=
  ∃ i j k m, a ≤ m ∧ m ≤ k ∧ k ≤ j ∧ j ≤ i ∧
    n = weight i + weight j + weight k + 2 * weight m

structure Sound (a : Nat) (s : Masks) : Prop where
  one : ∀ n, s.one.testBit n = true → RepOne a n
  two : ∀ n, s.two.testBit n = true → RepTwo a n
  three : ∀ n, s.three.testBit n = true → RepThree a n
  cover : ∀ n, s.cover.testBit n = true → RepFour a n

theorem bit_split (a b w n : Nat) (h : (a ||| (b <<< w)).testBit n = true) :
    a.testBit n = true ∨ ∃ r, b.testBit r = true ∧ n = r+w := by
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h with h | ⟨hle, hr⟩
  · exact Or.inl h
  · exact Or.inr ⟨n-w, hr, by omega⟩

theorem drop_mask {m mask n : Nat} (h : (m &&& mask).testBit n = true) :
    m.testBit n = true := by
  rw [Nat.testBit_and, Bool.and_eq_true] at h
  exact h.1

theorem step_sound (mask q a : Nat) (s : Masks) (hw : weight a = q)
    (h : Sound (a+1) s) : Sound a (step mask q s) := by
  let s' := step mask q s
  have one : ∀ n, s'.one.testBit n = true → RepOne a n := by
    intro n hn
    change (s.one ||| (1 <<< q)).testBit n = true at hn
    rcases bit_split _ _ _ _ hn with h₁ | ⟨r, hr, he⟩
    · obtain ⟨i, hi, rfl⟩ := h.one n h₁
      exact ⟨i, by omega, rfl⟩
    · have h0 := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hr
      exact ⟨a, le_rfl, by rw [hw]; omega⟩
  have two : ∀ n, s'.two.testBit n = true → RepTwo a n := by
    intro n hn
    change ((s.two ||| (s'.one <<< q)) &&& mask).testBit n = true at hn
    rcases bit_split _ _ _ _ (drop_mask hn) with h₂ | ⟨r, hr, he⟩
    · obtain ⟨i, j, hj, hji, rfl⟩ := h.two n h₂
      exact ⟨i, j, by omega, hji, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := one r hr
      exact ⟨i, a, le_rfl, hi, by rwa [hw]⟩
  have three : ∀ n, s'.three.testBit n = true → RepThree a n := by
    intro n hn
    change ((s.three ||| (s'.two <<< q)) &&& mask).testBit n = true at hn
    rcases bit_split _ _ _ _ (drop_mask hn) with h₃ | ⟨r, hr, he⟩
    · obtain ⟨i, j, k, hk, hkj, hji, rfl⟩ := h.three n h₃
      exact ⟨i, j, k, by omega, hkj, hji, rfl⟩
    · obtain ⟨i, j, hj, hji, rfl⟩ := two r hr
      exact ⟨i, j, a, le_rfl, hj, hji, by rwa [hw]⟩
  refine ⟨one, two, three, ?_⟩
  intro n hn
  change ((s.cover ||| (s'.three <<< (2*q))) &&& mask).testBit n = true at hn
  rcases bit_split _ _ _ _ (drop_mask hn) with h₄ | ⟨r, hr, he⟩
  · obtain ⟨i, j, k, m, hm, hmk, hkj, hji, rfl⟩ := h.cover n h₄
    exact ⟨i, j, k, m, by omega, hmk, hkj, hji, rfl⟩
  · obtain ⟨i, j, k, hk, hkj, hji, rfl⟩ := three r hr
    exact ⟨i, j, k, a, le_rfl, hk, hkj, hji, by rwa [hw]⟩

theorem foldr_sound (mask a : Nat) (qs : List Nat) (h : IndexedWeights a qs) :
    Sound a (qs.foldr (step mask) {}) := by
  induction qs generalizing a with
  | nil =>
    constructor <;> intro n hn <;> change (0:Nat).testBit n = true at hn <;> simp at hn
  | cons q qs ih =>
    exact step_sound mask q a _ h.1 (ih (a+1) h.2)

def certifiedWanted (upper : Nat) : Nat :=
  trim (progression 2 ((upper - 3200).log2+1) <<< 1) (2 * (upper-3200))

theorem oddWanted (upper n : Nat) (hlo : 3200 < n) (hhi : n ≤ upper) :
    (certifiedWanted upper).testBit (2*(n-3201)+1) = true := by
  rw [certifiedWanted, trim_bit _ _ _ (by omega), Nat.testBit_shiftLeft, Bool.and_eq_true,
    decide_eq_true_eq, progression_bit]
  have hpow := Nat.lt_log2_self (n := upper-3200)
  refine ⟨Nat.succ_pos _, n-3201, ?_, Nat.add_sub_cancel _ _⟩
  exact (show n-3201 ≤ upper-3200 by omega).trans_lt hpow

theorem covered (upper : Nat) (qs : List Nat) (hindex : IndexedWeights 1 qs)
    (hcover : ((packed (2*upper+1) qs >>> 6402) &&& certifiedWanted upper) =
      certifiedWanted upper) :
    ∀ n, 3200 < n → n ≤ upper → RepFour 1 (2*n+1) := by
  intro n hlo hhi
  have hbit : ((packed (2*upper+1) qs >>> 6402) &&& certifiedWanted upper).testBit
        (2*(n-3201)+1) = (certifiedWanted upper).testBit (2*(n-3201)+1) :=
    congrArg (fun m : Nat => m.testBit (2*(n-3201)+1)) hcover
  rw [Nat.testBit_and, oddWanted upper n hlo hhi, Bool.and_true, Nat.testBit_shiftRight,
    show 6402 + (2*(n-3201)+1) = 2*n+1 by omega] at hbit
  exact (foldr_sound _ 1 qs hindex).cover _ hbit

theorem indexed_append {i : Nat} {xs ys : List Nat}
    (hx : IndexedWeights i xs) (hy : IndexedWeights (i+xs.length) ys) :
    IndexedWeights i (xs++ys) := by
  induction xs generalizing i with
  | nil => simpa only [List.length_nil, Nat.add_zero, List.nil_append] using hy
  | cons x xs ih =>
    refine ⟨hx.1, ih hx.2 ?_⟩
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hy

theorem indexed_get {i : Nat} {xs : List Nat}
    (hx : IndexedWeights i xs) (j : Nat) (hj : j < xs.length) :
    Nat.nth Nat.Prime ((i+j)^2-1) = xs[j] := by
  induction xs generalizing i j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero => simpa using hx.1
    | succ j =>
      have hj' : j < xs.length := by simpa using hj
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih hx.2 j hj'

theorem count_of_indexed {i q : Nat} (h : Nat.nth Nat.Prime (i^2-1) = q) :
    Nat.count Nat.Prime q = i^2-1 := by
  rw [← h]
  exact Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime _

/-- Packed multiples that start in this interval at or beyond the square of d. -/
def segmentMarked (lo hi d : Nat) : Nat :=
  let k := max d (lo ⌈/⌉ d)
  progression d (((hi-lo)/d).log2 + 1) <<< (d*k-lo)

theorem segmentMarked_bit (lo hi d j : Nat) (hd : 0 < d) (hj : lo+j ≤ hi) :
    (segmentMarked lo hi d).testBit j = true ↔ d*d ≤ lo+j ∧ d ∣ lo+j := by
  let k := max d (lo ⌈/⌉ d)
  have hstart : lo ≤ d*k := (ceilDiv_le_iff_le_mul hd).mp (le_max_right _ _)
  have hsq : d*d ≤ d*k := Nat.mul_le_mul_left _ (le_max_left _ _)
  change (progression d (((hi-lo)/d).log2 + 1) <<< (d*k-lo)).testBit j = true ↔ _
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, progression_bit]
  constructor
  · rintro ⟨hle,t,_,ht⟩
    refine ⟨by omega,k+t,?_⟩
    rw [Nat.mul_add]
    omega
  · rintro ⟨hs, t, ht⟩
    have hkt : k ≤ t := max_le ((Nat.le_of_mul_le_mul_left (ht ▸ hs) hd))
      ((ceilDiv_le_iff_le_mul hd).mpr (by omega))
    have hm : d*k ≤ d*t := Nat.mul_le_mul_left _ hkt
    have he : d*(t-k) = d*t-d*k := Nat.mul_sub_left_distrib _ _ _
    have hbound : t-k ≤ (hi-lo)/d := (Nat.le_div_iff_mul_le hd).mpr (by
      rw [Nat.mul_comm, he]; omega)
    have hpow := Nat.lt_log2_self (n := (hi-lo)/d)
    exact ⟨by omega,t-k,by omega,by omega⟩

def segmentComposite (lo hi : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds =>
    (if 2 ≤ d ∧ d.minFac = d then segmentMarked lo hi d else 0) ||| segmentComposite lo hi ds

theorem segmentComposite_bit (lo hi j : Nat) (hj : lo+j ≤ hi) (ds : List Nat) :
    (segmentComposite lo hi ds).testBit j = (compositeMask hi ds).testBit (lo+j) := by
  induction ds with
  | nil => simp [segmentComposite, compositeMask]
  | cons d ds ih =>
    simp only [segmentComposite, compositeMask, Nat.testBit_or, ih]
    split
    next h =>
      congr 1
      apply Bool.eq_iff_iff.mpr
      rw [segmentMarked_bit lo hi d j (by omega) hj, marked_bit hi d _ (by omega) hj]
    next => simp

def segmentSieve (lo hi : Nat) : Nat :=
  ((1 <<< (hi-lo+1))-1) ^^^ (segmentComposite lo hi (List.range (hi.sqrt+1)) ||| (3 >>> lo))

theorem segmentSieve_bit (lo hi j : Nat) (hj : lo+j ≤ hi) :
    (segmentSieve lo hi).testBit j = (sieve hi).testBit (lo+j) := by
  simp only [segmentSieve, sieve, nonprimeMask, Nat.testBit_xor, Nat.testBit_or,
    Nat.testBit_shiftRight, segmentComposite_bit lo hi j hj, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.testBit_two_pow_sub_one, show j < hi-lo+1 by omega, show lo+j < hi+1 by omega]
theorem checkRanks_congr (hi m n a i : Nat) (qs : List Nat)
    (h : ∀ j, a ≤ j → j ≤ hi → m.testBit j = n.testBit j) :
    checkRanks hi m a i qs = checkRanks hi n a i qs := by
  induction qs generalizing a i with
  | nil => rfl
  | cons q qs ih =>
    by_cases hr : a ≤ q ∧ q ≤ hi
    · have hbit := h q hr.1 hr.2
      have hcount : rankBits (m >>> a) (q-a) = rankBits (n >>> a) (q-a) := by
        rw [rankBits_eq, rankBits_eq]
        apply count_congr_lt
        intro j hj
        rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, h (a+j) (by omega) (by omega)]
      rw [checkRanks, checkRanks, hbit, hcount, ih q (i+1) (fun j hq hj => h j (by omega) hj)]
    · simp [checkRanks, hr]

def alignedSegment (lo hi : Nat) : Nat := segmentSieve lo hi <<< lo

theorem indexedWeights_of_segment (hi lo i : Nat) (qs : List Nat)
    (hcount : Nat.count Nat.Prime lo = (i-1)^2-1)
    (h : checkRanks hi (alignedSegment lo hi) lo i qs = true) : IndexedWeights i qs := by
  apply indexedWeights_of_check hi lo i qs hcount
  rw [← checkRanks_congr hi (alignedSegment lo hi) (sieve hi) lo i qs]
  · exact h
  · intro j hj hhi
    simp only [alignedSegment, Nat.testBit_shiftLeft, decide_eq_true hj, Bool.true_and]
    rw [segmentSieve_bit lo hi (j-lo) (by omega), show lo+(j-lo) = j by omega]
/-- Four bits per byte value suffice to store its population count, including eight. -/
def bytePop (x : BitVec 8) : Nat :=
  (0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110 >>> (4*x.toNat)) &&& 15

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem bytePop_correct : ∀ x : BitVec 8, bytePop x = x.cpop.toNat := by
  decide +kernel

theorem popSplit (w len : Nat) (x : BitVec (w+len)) :
    x.cpop.toNat = (x.extractLsb' len w).cpop.toNat + (x.extractLsb' 0 len).cpop.toNat := by
  calc
    _ = (x.extractLsb' len w ++ x.extractLsb' 0 len).cpop.toNat :=
      congrArg (fun v : BitVec (w+len) => v.cpop.toNat) BitVec.extractLsb'_append_extractLsb'.symm
    _ = _ := BitVec.toNat_cpop_append

def wordPop16 (x : BitVec 16) : Nat :=
  bytePop (x.extractLsb' 8 8) + bytePop (x.extractLsb' 0 8)

theorem wordPop16_correct (x : BitVec 16) : wordPop16 x = x.cpop.toNat := by
  simp only [wordPop16, bytePop_correct]
  exact (popSplit 8 8 x).symm

def wordPop32 (x : BitVec 32) : Nat :=
  wordPop16 (x.extractLsb' 16 16) + wordPop16 (x.extractLsb' 0 16)

theorem wordPop32_correct (x : BitVec 32) : wordPop32 x = x.cpop.toNat := by
  simp only [wordPop32, wordPop16_correct]
  exact (popSplit 16 16 x).symm

theorem countWord32_correct (m n : Nat) (hn : n ≤ 32) :
    wordPop32 ((BitVec.ofNat n m).setWidth 32) = rankBits m n := by
  rw [wordPop32_correct, BitVec.toNat_cpop_setWidth_eq_of_le hn, rankBits, if_pos hn]

def fastRank (m len : Nat) : Nat :=
  if len ≤ 32 then wordPop32 ((BitVec.ofNat len m).setWidth 32)
  else
    let half := len / 2
    fastRank (trim m half) half + fastRank (m >>> half) (len-half)
termination_by len
decreasing_by all_goals omega

theorem fastRank_eq (m len : Nat) : fastRank m len = rankBits m len := by
  by_cases h : len ≤ 32
  · rw [fastRank, if_pos h, countWord32_correct m len h]
  · rw [fastRank, if_neg h, rankBits, if_neg h]
    dsimp only
    rw [fastRank_eq (trim m (len/2)) (len/2), fastRank_eq (m >>> (len/2)) (len-len/2)]
termination_by len
decreasing_by all_goals omega

def checkFast (bound bits : Nat) (a i : Nat) : List Nat → Bool
  | [] => true
  | q :: qs =>
    decide (a ≤ q ∧ q ≤ bound) &&
      bits.testBit q &&
      decide (fastRank (bits >>> a) (q-a) = (i^2-1) - ((i-1)^2-1)) &&
      checkFast bound bits q (i+1) qs

theorem checkFast_eq (bound bits a i : Nat) (qs : List Nat) :
    checkFast bound bits a i qs = checkRanks bound bits a i qs := by
  induction qs generalizing a i with
  | nil => rfl
  | cons q qs ih => simp only [checkFast, checkRanks, fastRank_eq, ih]

theorem indexedWeights_of_fastSegment (hi lo i : Nat) (qs : List Nat)
    (hcount : Nat.count Nat.Prime lo = (i-1)^2-1)
    (h : checkFast hi (alignedSegment lo hi) lo i qs = true) : IndexedWeights i qs := by
  apply indexedWeights_of_segment hi lo i qs hcount
  rwa [← checkFast_eq]

def weights00 : List Nat := [
  2, 7, 23, 53, 97, 151, 227, 311, 419, 541, 661, 827,
  1009, 1193, 1427, 1619, 1879, 2143, 2437, 2741, 3083, 3461, 3803, 4211,
  4637, 5051, 5519, 6007, 6481, 6997, 7573, 8161, 8737, 9341, 9931, 10627,
  11321, 12049, 12743, 13499, 14327, 15101, 15877, 16747, 17609, 18461, 19471, 20393,
  21391, 22307, 23327, 24359, 25469, 26573, 27739, 28793, 30047, 31223, 32429, 33613,
  34849, 36217, 37501, 38873, 40231, 41641, 42943, 44497, 45989, 47527, 49037, 50543,
  52121, 53731, 55381, 56951, 58579, 60289, 62081, 63809, 65687, 67493, 69401, 71263,
  73061, 75017, 77017, 78977, 80929, 82891, 85037, 87151, 89303, 91381, 93479, 95603,
  97879, 100169
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify00 (hcount : Nat.count Nat.Prime 0 = 0^2-1) :
    IndexedWeights 1 weights00 := by
  apply indexedWeights_of_fastSegment 100169 0
  · exact hcount
  · decide +kernel

def weights01 : List Nat := [
  102329, 104729, 107053, 109441, 111863, 114299, 116791, 119237, 121631, 124181, 126719, 129281,
  131927, 134587, 137143, 139861, 142537, 145441, 148193, 150901, 153611, 156593, 159521, 162493,
  165457, 168523, 171529, 174487, 177589, 180503, 183697, 186757, 189913, 193093, 196429, 199673
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify01 (hcount : Nat.count Nat.Prime 100169 = 98^2-1) :
    IndexedWeights 99 weights01 := by
  apply indexedWeights_of_fastSegment 199673 100169
  · exact hcount
  · decide +kernel

def weights02 : List Nat := [
  202987, 206303, 209569, 212981, 216481, 219829, 223259, 226777, 230123, 233879, 237607, 241177,
  244691, 248299, 251969, 255709, 259547, 263437, 267217, 270841, 274847, 278701, 282589, 286609,
  290659, 294809, 299017, 303053
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify02 (hcount : Nat.count Nat.Prime 199673 = 134^2-1) :
    IndexedWeights 135 weights02 := by
  apply indexedWeights_of_fastSegment 303053 199673
  · exact hcount
  · decide +kernel

def weights22 : List Nat := [
  306949, 311237, 315409, 319391, 323567, 327689, 331943, 336317, 340723, 345019, 349403, 353807,
  358291, 362953, 367277, 372223, 376687, 381373, 385997, 390707, 395147, 399941
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify22 (hcount : Nat.count Nat.Prime 303053 = 162^2-1) :
    IndexedWeights 163 weights22 := by
  apply indexedWeights_of_fastSegment 399941 303053
  · exact hcount
  · decide +kernel

def weights03 : List Nat := [
  405029, 409823, 414677, 419429, 424243, 429361, 433981, 438979, 443837, 449131, 454213, 459341,
  464663, 469753, 474779, 479909, 485263, 490499, 495679, 500957, 506461, 511873, 517277, 522623,
  528043, 533693, 539237, 544919, 550631, 556351, 562103, 567871, 573451, 579199, 584981, 590659,
  596569
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify03 (hcount : Nat.count Nat.Prime 399941 = 184^2-1) :
    IndexedWeights 185 weights03 := by
  apply indexedWeights_of_fastSegment 596569 399941
  · exact hcount
  · decide +kernel

def weights04 : List Nat := [
  602411, 608369, 614219, 620201, 626333, 632483, 638669, 644911, 651103, 657269, 663517, 669733,
  675929, 682147, 688447, 694867, 701399, 707671, 713927, 720683, 727003, 733561, 740053, 747113,
  753721, 760411, 766873, 773609, 780469, 787217, 793957, 800663
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify04 (hcount : Nat.count Nat.Prime 596569 = 221^2-1) :
    IndexedWeights 222 weights04 := by
  apply indexedWeights_of_fastSegment 800663 596569
  · exact hcount
  · decide +kernel

def weights05 : List Nat := [
  807689, 814631, 821641, 828383, 835459, 842531, 849743, 856927, 864053, 870931, 878291, 885509,
  892757, 900169, 907469, 914887, 922283, 929561, 937121, 944551, 952277, 960077, 967667, 975049,
  983119, 990893, 998561
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify05 (hcount : Nat.count Nat.Prime 800663 = 253^2-1) :
    IndexedWeights 254 weights05 := by
  apply indexedWeights_of_fastSegment 998561 800663
  · exact hcount
  · decide +kernel

def weights06 : List Nat := [
  1006237, 1013819, 1021441, 1029383, 1037329, 1045241, 1053491, 1061617, 1069603, 1077707, 1085719, 1093739,
  1101871, 1109813, 1117867, 1126399, 1134443, 1142891, 1151251, 1159523, 1167689, 1176137, 1184291, 1192673,
  1201241
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify06 (hcount : Nat.count Nat.Prime 998561 = 280^2-1) :
    IndexedWeights 281 weights06 := by
  apply indexedWeights_of_fastSegment 1201241 998561
  · exact hcount
  · decide +kernel

def weights07 : List Nat := [
  1210259, 1218583, 1227323, 1236439, 1244989, 1253831, 1262311, 1270897, 1279819, 1288541, 1297487, 1306519,
  1315627, 1324429, 1333613, 1342531, 1351853, 1360943, 1370099, 1379107, 1388381, 1397491
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify07 (hcount : Nat.count Nat.Prime 1201241 = 305^2-1) :
    IndexedWeights 306 weights07 := by
  apply indexedWeights_of_fastSegment 1397491 1201241
  · exact hcount
  · decide +kernel

def weights08 : List Nat := [
  1406879, 1416293, 1425863, 1434883, 1444309, 1453681, 1462939, 1472623, 1482049, 1491583, 1501139, 1510417,
  1520203, 1530037, 1539991, 1549817, 1559449, 1569473, 1579399, 1589453, 1599583
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify08 (hcount : Nat.count Nat.Prime 1397491 = 327^2-1) :
    IndexedWeights 328 weights08 := by
  apply indexedWeights_of_fastSegment 1599583 1397491
  · exact hcount
  · decide +kernel

def weights09 : List Nat := [
  1609301, 1619417, 1629211, 1639459, 1649671, 1659667, 1669649, 1679693, 1690253, 1700339, 1710613, 1721143,
  1731659, 1742101, 1752239, 1763231, 1773689, 1783907, 1794647
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify09 (hcount : Nat.count Nat.Prime 1599583 = 348^2-1) :
    IndexedWeights 349 weights09 := by
  apply indexedWeights_of_fastSegment 1794647 1599583
  · exact hcount
  · decide +kernel

def weights10 : List Nat := [
  1805147, 1815559, 1826197, 1836959, 1847689, 1858261, 1868723, 1879789, 1890487, 1901507, 1912429, 1923277,
  1934117, 1945043, 1956011, 1967347, 1978993, 1990081, 2000939
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify10 (hcount : Nat.count Nat.Prime 1794647 = 367^2-1) :
    IndexedWeights 368 weights10 := by
  apply indexedWeights_of_fastSegment 2000939 1794647
  · exact hcount
  · decide +kernel

def weights11 : List Nat := [
  2012011, 2023061, 2034211, 2045731, 2057303, 2068513, 2080027, 2091587, 2103067, 2114627, 2126191, 2137679,
  2149171, 2160553, 2172491, 2184283, 2195989
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify11 (hcount : Nat.count Nat.Prime 2000939 = 386^2-1) :
    IndexedWeights 387 weights11 := by
  apply indexedWeights_of_fastSegment 2195989 2000939
  · exact hcount
  · decide +kernel

def weights12 : List Nat := [
  2207939, 2220041, 2231737, 2243723, 2255717, 2267263, 2278979, 2291351, 2303359, 2315597, 2327887, 2340259,
  2352641, 2364647, 2377069, 2389243, 2401537
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify12 (hcount : Nat.count Nat.Prime 2195989 = 403^2-1) :
    IndexedWeights 404 weights12 := by
  apply indexedWeights_of_fastSegment 2401537 2195989
  · exact hcount
  · decide +kernel

def weights13 : List Nat := [
  2414053, 2426387, 2439133, 2451467, 2463833, 2476489, 2488909, 2501761, 2514221, 2526697, 2539429, 2552507,
  2565139, 2577697, 2590349
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify13 (hcount : Nat.count Nat.Prime 2401537 = 420^2-1) :
    IndexedWeights 421 weights13 := by
  apply indexedWeights_of_fastSegment 2590349 2401537
  · exact hcount
  · decide +kernel

def weights14 : List Nat := [
  2603369, 2616209, 2629483, 2642179, 2655047, 2667983, 2681267, 2694217, 2707283, 2720147, 2733749, 2747179,
  2760617, 2773699, 2787119, 2800601
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify14 (hcount : Nat.count Nat.Prime 2590349 = 435^2-1) :
    IndexedWeights 436 weights14 := by
  apply indexedWeights_of_fastSegment 2800601 2590349
  · exact hcount
  · decide +kernel

def weights15 : List Nat := [
  2813479, 2826793, 2839957, 2853647, 2867099, 2881163, 2894813, 2908483, 2922133, 2936023, 2949887, 2963683,
  2977619, 2991421
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify15 (hcount : Nat.count Nat.Prime 2800601 = 451^2-1) :
    IndexedWeights 452 weights15 := by
  apply indexedWeights_of_fastSegment 2991421 2800601
  · exact hcount
  · decide +kernel

def weights16 : List Nat := [
  3004993, 3019153, 3033169, 3047309, 3061459, 3075341, 3089239, 3103543, 3117589, 3131503, 3146141, 3160193,
  3174337, 3188761
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify16 (hcount : Nat.count Nat.Prime 2991421 = 465^2-1) :
    IndexedWeights 466 weights16 := by
  apply indexedWeights_of_fastSegment 3188761 2991421
  · exact hcount
  · decide +kernel

def weights17 : List Nat := [
  3202519, 3216779, 3231287, 3245689, 3260137, 3274753, 3289229, 3304237, 3318599, 3333383, 3348061, 3363629,
  3377873, 3392723
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify17 (hcount : Nat.count Nat.Prime 3188761 = 479^2-1) :
    IndexedWeights 480 weights17 := by
  apply indexedWeights_of_fastSegment 3392723 3188761
  · exact hcount
  · decide +kernel

def weights18 : List Nat := [
  3407279, 3422131, 3436817, 3451417, 3466891, 3482341, 3497861, 3512909, 3528521, 3543919, 3559097, 3574309,
  3589693
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify18 (hcount : Nat.count Nat.Prime 3392723 = 493^2-1) :
    IndexedWeights 494 weights18 := by
  apply indexedWeights_of_fastSegment 3589693 3392723
  · exact hcount
  · decide +kernel

def weights19 : List Nat := [
  3604789, 3619613, 3634637, 3650533, 3666119, 3681131, 3696557, 3712253, 3727387, 3743011, 3758507, 3774769,
  3790547
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify19 (hcount : Nat.count Nat.Prime 3589693 = 506^2-1) :
    IndexedWeights 507 weights19 := by
  apply indexedWeights_of_fastSegment 3790547 3589693
  · exact hcount
  · decide +kernel

def weights20 : List Nat := [
  3806119, 3821681, 3837497, 3853301, 3869213, 3885461, 3901103, 3917119, 3932921, 3948809, 3965309, 3981403,
  3998191
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify20 (hcount : Nat.count Nat.Prime 3790547 = 519^2-1) :
    IndexedWeights 520 weights20 := by
  apply indexedWeights_of_fastSegment 3998191 3790547
  · exact hcount
  · decide +kernel

def weights21 : List Nat := [
  4014277, 4030393, 4046087, 4062533, 4078663, 4094953, 4111271, 4128199, 4144981, 4161331, 4177939, 4194167
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2500000 in
theorem certify21 (hcount : Nat.count Nat.Prime 3998191 = 532^2-1) :
    IndexedWeights 533 weights21 := by
  apply indexedWeights_of_fastSegment 4194167 3998191
  · exact hcount
  · decide +kernel

end A389525Pilot

namespace A389525Pilot

private def suffix21 : List Nat := weights21
private def suffix20 : List Nat := weights20 ++ suffix21
private def suffix19 : List Nat := weights19 ++ suffix20
private def suffix18 : List Nat := weights18 ++ suffix19
private def suffix17 : List Nat := weights17 ++ suffix18
private def suffix16 : List Nat := weights16 ++ suffix17
private def suffix15 : List Nat := weights15 ++ suffix16
private def suffix14 : List Nat := weights14 ++ suffix15
private def suffix13 : List Nat := weights13 ++ suffix14
private def suffix12 : List Nat := weights12 ++ suffix13
private def suffix11 : List Nat := weights11 ++ suffix12
private def suffix10 : List Nat := weights10 ++ suffix11
private def suffix09 : List Nat := weights09 ++ suffix10
private def suffix08 : List Nat := weights08 ++ suffix09
private def suffix07 : List Nat := weights07 ++ suffix08
private def suffix06 : List Nat := weights06 ++ suffix07
private def suffix05 : List Nat := weights05 ++ suffix06
private def suffix04 : List Nat := weights04 ++ suffix05
private def suffix03 : List Nat := weights03 ++ suffix04
private def suffix22 : List Nat := weights22 ++ suffix03
private def suffix02 : List Nat := weights02 ++ suffix22
private def suffix01 : List Nat := weights01 ++ suffix02
private def suffix00 : List Nat := weights00 ++ suffix01

private def certifiedWeights : List Nat := suffix00

private theorem weightsIndexed : IndexedWeights 1 certifiedWeights := by
  have rank00 := certify00 (Nat.count_zero Nat.Prime)
  have rank01 := certify01 (count_of_indexed (i := 98) (q := 100169)
    (indexed_get rank00 97 (by decide)))
  have rank02 := certify02 (count_of_indexed (i := 134) (q := 199673)
    (indexed_get rank01 35 (by decide)))
  have rank22 := certify22 (count_of_indexed (i := 162) (q := 303053)
    (indexed_get rank02 27 (by decide)))
  have rank03 := certify03 (count_of_indexed (i := 184) (q := 399941)
    (indexed_get rank22 21 (by decide)))
  have rank04 := certify04 (count_of_indexed (i := 221) (q := 596569)
    (indexed_get rank03 36 (by decide)))
  have rank05 := certify05 (count_of_indexed (i := 253) (q := 800663)
    (indexed_get rank04 31 (by decide)))
  have rank06 := certify06 (count_of_indexed (i := 280) (q := 998561)
    (indexed_get rank05 26 (by decide)))
  have rank07 := certify07 (count_of_indexed (i := 305) (q := 1201241)
    (indexed_get rank06 24 (by decide)))
  have rank08 := certify08 (count_of_indexed (i := 327) (q := 1397491)
    (indexed_get rank07 21 (by decide)))
  have rank09 := certify09 (count_of_indexed (i := 348) (q := 1599583)
    (indexed_get rank08 20 (by decide)))
  have rank10 := certify10 (count_of_indexed (i := 367) (q := 1794647)
    (indexed_get rank09 18 (by decide)))
  have rank11 := certify11 (count_of_indexed (i := 386) (q := 2000939)
    (indexed_get rank10 18 (by decide)))
  have rank12 := certify12 (count_of_indexed (i := 403) (q := 2195989)
    (indexed_get rank11 16 (by decide)))
  have rank13 := certify13 (count_of_indexed (i := 420) (q := 2401537)
    (indexed_get rank12 16 (by decide)))
  have rank14 := certify14 (count_of_indexed (i := 435) (q := 2590349)
    (indexed_get rank13 14 (by decide)))
  have rank15 := certify15 (count_of_indexed (i := 451) (q := 2800601)
    (indexed_get rank14 15 (by decide)))
  have rank16 := certify16 (count_of_indexed (i := 465) (q := 2991421)
    (indexed_get rank15 13 (by decide)))
  have rank17 := certify17 (count_of_indexed (i := 479) (q := 3188761)
    (indexed_get rank16 13 (by decide)))
  have rank18 := certify18 (count_of_indexed (i := 493) (q := 3392723)
    (indexed_get rank17 13 (by decide)))
  have rank19 := certify19 (count_of_indexed (i := 506) (q := 3589693)
    (indexed_get rank18 12 (by decide)))
  have rank20 := certify20 (count_of_indexed (i := 519) (q := 3790547)
    (indexed_get rank19 12 (by decide)))
  have rank21 := certify21 (count_of_indexed (i := 532) (q := 3998191)
    (indexed_get rank20 12 (by decide)))
  have joined21 : IndexedWeights 533 suffix21 := rank21
  have joined20 : IndexedWeights 520 suffix20 :=
    indexed_append (xs := weights20) (ys := suffix21) rank20 joined21
  have joined19 : IndexedWeights 507 suffix19 :=
    indexed_append (xs := weights19) (ys := suffix20) rank19 joined20
  have joined18 : IndexedWeights 494 suffix18 :=
    indexed_append (xs := weights18) (ys := suffix19) rank18 joined19
  have joined17 : IndexedWeights 480 suffix17 :=
    indexed_append (xs := weights17) (ys := suffix18) rank17 joined18
  have joined16 : IndexedWeights 466 suffix16 :=
    indexed_append (xs := weights16) (ys := suffix17) rank16 joined17
  have joined15 : IndexedWeights 452 suffix15 :=
    indexed_append (xs := weights15) (ys := suffix16) rank15 joined16
  have joined14 : IndexedWeights 436 suffix14 :=
    indexed_append (xs := weights14) (ys := suffix15) rank14 joined15
  have joined13 : IndexedWeights 421 suffix13 :=
    indexed_append (xs := weights13) (ys := suffix14) rank13 joined14
  have joined12 : IndexedWeights 404 suffix12 :=
    indexed_append (xs := weights12) (ys := suffix13) rank12 joined13
  have joined11 : IndexedWeights 387 suffix11 :=
    indexed_append (xs := weights11) (ys := suffix12) rank11 joined12
  have joined10 : IndexedWeights 368 suffix10 :=
    indexed_append (xs := weights10) (ys := suffix11) rank10 joined11
  have joined09 : IndexedWeights 349 suffix09 :=
    indexed_append (xs := weights09) (ys := suffix10) rank09 joined10
  have joined08 : IndexedWeights 328 suffix08 :=
    indexed_append (xs := weights08) (ys := suffix09) rank08 joined09
  have joined07 : IndexedWeights 306 suffix07 :=
    indexed_append (xs := weights07) (ys := suffix08) rank07 joined08
  have joined06 : IndexedWeights 281 suffix06 :=
    indexed_append (xs := weights06) (ys := suffix07) rank06 joined07
  have joined05 : IndexedWeights 254 suffix05 :=
    indexed_append (xs := weights05) (ys := suffix06) rank05 joined06
  have joined04 : IndexedWeights 222 suffix04 :=
    indexed_append (xs := weights04) (ys := suffix05) rank04 joined05
  have joined03 : IndexedWeights 185 suffix03 :=
    indexed_append (xs := weights03) (ys := suffix04) rank03 joined04
  have joined22 : IndexedWeights 163 suffix22 :=
    indexed_append (xs := weights22) (ys := suffix03) rank22 joined03
  have joined02 : IndexedWeights 135 suffix02 :=
    indexed_append (xs := weights02) (ys := suffix22) rank02 joined22
  have joined01 : IndexedWeights 99 suffix01 :=
    indexed_append (xs := weights01) (ys := suffix02) rank01 joined02
  have joined00 : IndexedWeights 1 suffix00 :=
    indexed_append (xs := weights00) (ys := suffix01) rank00 joined01
  exact joined00

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem arithmeticCover :
    ((packed (2 * 7700000 + 1) certifiedWeights >>> 6402) &&&
      certifiedWanted 7700000) = certifiedWanted 7700000 := by
  decide +kernel

end A389525Pilot

open A389525Pilot in
theorem OMA.solution : OMA.R_oeis_a389525_R1.H1 :=
  covered 7700000 certifiedWeights weightsIndexed arithmeticCover
