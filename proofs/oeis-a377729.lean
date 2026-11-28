import OMAStatements.S_oeis_a377729

/-!
David A. Corneth exhibited two equal sums of distinct polygonal numbers in A377729.
I prove their minimality and exact multiplicity, then derive the generating function.
Source: https://oeis.org/A377729. Credit: @Aryan-Poonacha.
-/

namespace Polygonal
open OMA.S_oeis_a377729

private theorem doubleP (n k : ℕ) :
    (2 : ℤ) * P n k = ((n-2 : ℕ) : ℤ) * k * ((k:ℤ)-1) + 2*k := by
  cases k with
  | zero => simp [P]
  | succ k =>
    have even : 2 ∣ (n-2) * (k+1) * k := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using (dvd_mul_of_dvd_right (Nat.two_dvd_mul_add_one k) (n-2))
    have v := Nat.div_mul_cancel even
    unfold P
    simp only [Nat.add_one_sub_one, Nat.cast_add, Nat.cast_one] at *
    have z : (((n-2)*(k+1)*k/2 : ℕ) : ℤ)*2 = ((n-2:ℕ):ℤ)*(k+1)*k := by exact_mod_cast v
    linarith

private theorem monoP (n : ℕ) : StrictMono (P n) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h := doubleP n k
  have h' := doubleP n (k+1)
  push_cast at h'
  exact_mod_cast (show (P n k:ℤ) < P n (k+1) by
    nlinarith [mul_nonneg (Nat.cast_nonneg (n-2) : (0:ℤ) ≤ _) (Nat.cast_nonneg k : (0:ℤ) ≤ _)])

private def seg (n : ℕ) := Finset.Icc 1 n
private def weight (n : ℕ) (s : Finset ℕ) := ∑ j ∈ s, P n j
private def base (n : ℕ) := weight n (seg n)

-- Removing the common indices leaves equally many old and new terms.
private theorem windowBounds {n m : ℕ} (s : Finset ℕ) (card : s.card = n)
    (pos : ∀ j ∈ s, 0 < j) (wt : weight n s = m) :
    (∀ j ∈ seg n, j ∉ s → base n + P n (n+1) ≤ m + P n j) ∧
    (∀ j ∈ s, n < j → base n + P n j ≤ m + P n n) := by
  let I := seg n
  let A := s \ I
  let B := I \ s
  have cI : I.card = n := by simp [I, seg]
  have cAB : A.card = B.card := by
    change (s \ I).card = (I \ s).card
    rw [Finset.card_sdiff, Finset.card_sdiff, card, cI, Finset.inter_comm]
  have small (j) (hj : j ∈ B) : P n j ≤ P n n :=
    (monoP n).monotone (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hj).1).2
  have large (j) (hj : j ∈ A) : P n (n+1) ≤ P n j := by
    apply (monoP n).monotone
    obtain ⟨h,hn⟩ := Finset.mem_sdiff.mp hj
    have := pos j h
    change j ∉ Finset.Icc 1 n at hn
    simp at hn
    omega
  have sumB : weight n B ≤ B.card * P n n := by
    simpa [weight] using Finset.sum_le_sum small
  have sumA : A.card * P n (n+1) ≤ weight n A := by
    simpa [weight] using Finset.sum_le_sum large
  have balance : base n + weight n A = m + weight n B := by
    have sa := Finset.sum_sdiff (f := P n) (Finset.inter_subset_left (s₁:=s) (s₂:=I))
    have sb := Finset.sum_sdiff (f := P n) (Finset.inter_subset_right (s₁:=s) (s₂:=I))
    have e : s \ (s ∩ I) = A := by ext; simp [A]
    have e' : I \ (s ∩ I) = B := by ext; simp [B, and_comm]
    rw [e] at sa
    rw [e'] at sb
    change (∑ j ∈ I, P n j) + (∑ j ∈ A, P n j) = m + (∑ j ∈ B, P n j)
    unfold weight at wt
    omega
  have rising : P n n ≤ P n (n+1) := (monoP n).monotone (Nat.le_succ n)
  constructor
  · intro j hj hn
    have mem : j ∈ B := Finset.mem_sdiff.mpr ⟨hj,hn⟩
    have ce := Finset.card_erase_add_one mem
    have se := Finset.sum_erase_add B (P n) mem
    have bound : weight n (B.erase j) ≤ (B.erase j).card * P n n := by
      simpa [weight] using Finset.sum_le_sum (fun i hi => small i (Finset.mem_of_mem_erase hi))
    rw [cAB, ← ce, Nat.add_mul, one_mul] at sumA
    have hle := Nat.mul_le_mul_left (B.erase j).card rising
    change weight n (B.erase j) + P n j = weight n B at se
    omega
  · intro j hj hn
    have mem : j ∈ A := Finset.mem_sdiff.mpr ⟨hj, fun h => by
      have := (Finset.mem_Icc.mp h).2; omega⟩
    have ce := Finset.card_erase_add_one mem
    have se := Finset.sum_erase_add A (P n) mem
    have bound : (A.erase j).card * P n (n+1) ≤ weight n (A.erase j) := by
      simpa [weight] using Finset.sum_le_sum (fun i hi => large i (Finset.mem_of_mem_erase hi))
    rw [← cAB, ← ce, Nat.add_mul, one_mul] at sumB
    have hle := Nat.mul_le_mul_left (A.erase j).card rising
    change weight n (A.erase j) + P n j = weight n A at se
    omega

private def windows (len cnt : ℕ) := (seg len).powersetCard cnt
private def extend (lo : ℕ) (r : Finset ℕ) := seg lo ∪ r.image (lo+·)
private def score (n lo : ℕ) (r : Finset ℕ) := weight n (seg lo) + ∑ i ∈ r, P n (lo+i)

-- A surviving representation is uniquely the forced prefix and a translated window.
private theorem window_count {n lo len q : ℕ} (hlo : lo ≤ n)
    (cover : ∀ s : Finset ℕ, s.card = n → (∀ i ∈ s, 0 < i) → weight n s ≤ q →
        seg lo ⊆ s ∧ s ⊆ seg (lo+len)) (m : ℕ) (hm : m ≤ q) :
    ways n m = ((windows len (n-lo)).filter (fun r => score n lo r = m)).card := by
  classical
  let good := (windows len (n-lo)).filter (fun r => score n lo r = m)
  have pack (r) (hr : r ∈ windows len (n-lo)) :
      (extend lo r).card = n ∧ (∀ i ∈ extend lo r, 0 < i) ∧
      weight n (extend lo r) = score n lo r := by
    obtain ⟨sub, card⟩ := Finset.mem_powersetCard.mp hr
    have dis : Disjoint (seg lo) (r.image (lo+·)) := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi'
      have := (Finset.mem_Icc.mp (sub hj)).1
      have := (Finset.mem_Icc.mp hi).2
      omega
    refine ⟨?_, ?_, ?_⟩
    · rw [extend, Finset.card_union_of_disjoint dis, Finset.card_image_of_injective _ (add_right_injective lo),card]
      simp [seg]; omega
    · intro i hi
      rcases Finset.mem_union.mp hi with h | h
      · exact (Finset.mem_Icc.mp h).1
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        have := (Finset.mem_Icc.mp (sub hj)).1
        omega
    · simp [weight, extend, score, Finset.sum_union dis, Finset.sum_image (add_right_injective lo).injOn]
  let f (r : ↥good) : {s : Finset ℕ // s.card = n ∧ (∀ x ∈ s, ∃ k, 0 < k ∧ x = P n k) ∧ ∑ x ∈ s, x = m} :=
    ⟨(extend lo r.val).image (P n), by
      obtain ⟨hr,hs⟩ := Finset.mem_filter.mp r.prop
      obtain ⟨card,pos,w⟩ := pack _ hr
      refine ⟨(Finset.card_image_of_injective _ (monoP n).injective).trans card, ?_, ?_⟩
      · intro x hx
        obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
        exact ⟨k,pos k hk,rfl⟩
      · rw [Finset.sum_image (monoP n).injective.injOn]
        exact w.trans hs⟩
  have bij : Function.Bijective f := by
    constructor
    · intro r t e
      have eq : extend lo r.val = extend lo t.val := Finset.image_injective (monoP n).injective (congrArg Subtype.val e)
      have member (s : ↥good) (j : ℕ) (hj : j ≠ 0) : lo+j ∈ extend lo s.val ↔ j ∈ s.val := by
        simp [extend,seg, show ¬lo+j≤lo by omega]
      apply Subtype.ext
      ext j
      by_cases z : j = 0
      · subst j
        have h (s : ↥good) : 0 ∉ s.val := fun h0 => by
          have h1 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp s.prop).1).1 h0
          exact (by simp [seg] at h1)
        simp [h]
      · rw [← member r j z, ← member t j z, eq]
    · rintro ⟨s,hs1,hs2,hs3⟩
      let t := s.preimage (P n) (monoP n).injective.injOn
      have img : t.image (P n) = s := by
        rw [Finset.image_preimage]; apply Finset.filter_true_of_mem
        intro x hx
        rcases hs2 x hx with ⟨k,_,rfl⟩
        exact ⟨k,rfl⟩
      have tc : t.card = n := by rw [← hs1, ← img, Finset.card_image_of_injective _ (monoP n).injective]
      have tp : ∀ i ∈ t, 0 < i := by
        intro i hi
        obtain ⟨k,hk,he⟩ := hs2 (P n i) (Finset.mem_preimage.mp hi)
        exact (monoP n).injective he ▸ hk
      have tw : weight n t = m := by
        rw [← img, Finset.sum_image (monoP n).injective.injOn] at hs3
        exact hs3
      obtain ⟨h1,h2⟩ := cover t tc tp (tw.le.trans hm)
      let r := (t \ seg lo).image (· - lo)
      have recov : r.image (lo+·) = t \ seg lo := by
        ext j
        simp only [r, Finset.mem_image, Finset.mem_sdiff, seg, Finset.mem_Icc]
        constructor
        · rintro ⟨i,⟨k,⟨hk,hk'⟩,rfl⟩,rfl⟩
          have := tp k hk
          have : lo+(k-lo)=k := by omega
          simp [this,hk,hk']
        · rintro ⟨hj,hj'⟩
          have := tp j hj
          exact ⟨j-lo,⟨j,⟨hj,hj'⟩,rfl⟩,by omega⟩
      have re : extend lo r = t := by rw [extend,recov,Finset.union_comm,Finset.sdiff_union_of_subset h1]
      have hr : r ∈ windows len (n-lo) := by
        apply Finset.mem_powersetCard.mpr
        constructor
        · intro j hj
          obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
          obtain ⟨hk,hl⟩ := Finset.mem_sdiff.mp hk
          have hh := Finset.mem_Icc.mp (h2 hk)
          change k ∉ Finset.Icc 1 lo at hl
          simp only [Finset.mem_Icc, not_and] at hl
          apply Finset.mem_Icc.mpr; omega
        · calc r.card = (r.image (lo+·)).card := (Finset.card_image_of_injective _ (add_right_injective lo)).symm
               _ = n-lo := by rw [recov, Finset.card_sdiff_of_subset h1, tc]; simp [seg]
      have hs : score n lo r = m := by rw [← (pack r hr).2.2,re,tw]
      refine ⟨⟨r, Finset.mem_filter.mpr ⟨hr,hs⟩⟩, Subtype.ext ?_⟩
      change (extend lo r).image (P n) = s
      rw [re,img]
  calc ways n m = Nat.card (↥good) := (Nat.card_congr (Equiv.ofBijective f bij)).symm
       _ = good.card := by simp [Nat.card_eq_fintype_card]

private theorem cover_of_bounds {n lo len q : ℕ} (hl : lo ≤ n) (hh : n ≤ lo+len)
    (left : lo = 0 ∨ q + P n lo < base n + P n (n+1))
    (right : q + P n n < base n + P n (lo+len+1)) :
    ∀ s : Finset ℕ, s.card = n → (∀ j ∈ s, 0 < j) → weight n s ≤ q →
      seg lo ⊆ s ∧ s ⊆ seg (lo+len) := by
  intro s hc hp hw
  obtain ⟨L,R⟩ := windowBounds s hc hp rfl
  constructor
  · intro j hj
    obtain ⟨hj,hjl⟩ := Finset.mem_Icc.mp hj
    by_contra hn
    have h := L j (Finset.mem_Icc.mpr ⟨hj,hjl.trans hl⟩) hn
    have mm := (monoP n).monotone hjl
    omega
  · intro j hj
    apply Finset.mem_Icc.mpr
    refine ⟨hp j hj,?_⟩
    by_contra! h
    have e := R j hj (lt_of_le_of_lt hh h)
    have mm : P n (lo+len+1) ≤ P n j := (monoP n).monotone h
    omega

private def scores (n lo len : ℕ) : Multiset ℕ :=
  (windows len (n-lo)).val.map (score n lo)

private theorem counted {n lo len q : ℕ}
    (hl : lo ≤ n) (hh : n ≤ lo+len)
    (left : lo = 0 ∨ q + P n lo < base n + P n (n+1))
    (right : q + P n n < base n + P n (lo+len+1)) (m : ℕ) (hm : m ≤ q) :
    ways n m = (scores n lo len).count m := by
  rw [window_count hl (cover_of_bounds hl hh left right) m hm]
  simp [scores, Multiset.count_map, Finset.card_def, eq_comm]

private def smallCert (n lo len q : ℕ) : Bool :=
  let v := (scores n lo len).filter (· ≤ q)
  decide (lo ≤ n ∧ n ≤ lo+len ∧ (lo = 0 ∨ q+P n lo < base n+P n (n+1)) ∧
    q+P n n < base n+P n (lo+len+1) ∧ v.count q = 2 ∧
    ∀ y ∈ v, y < q → v.count y ≠ 2)

private theorem small_result {n lo len q : ℕ} (h : smallCert n lo len q = true) : a n = q := by
  simp only [smallCert,decide_eq_true_eq] at h
  obtain ⟨hl,hh,left,right,eq,unique⟩ := h
  let v := scores n lo len
  have hc (m) (hm : m ≤ q) : ways n m = (v.filter (· ≤ q)).count m := by
    rw [counted hl hh left right m hm]
    simp [v,hm]
  apply IsLeast.csInf_eq
  refine ⟨(hc q le_rfl).trans eq, ?_⟩
  intro m he
  change ways n m = 2 at he
  by_contra! hm
  have h2 := (hc m hm.le).symm.trans he
  have hmem := Multiset.count_pos.mp (show 0 < (v.filter (· ≤ q)).count m by omega)
  exact unique m hmem hm h2
private theorem partialSum (n k : ℕ) :
    (6 : ℤ) * weight n (seg k) =
    ((n-2 : ℕ):ℤ) * ((k:ℤ)^3-k) + 3*k*(k+1) := by
  induction k with
  | zero => simp [weight,seg]
  | succ k ih =>
    unfold weight seg at *
    rw [Finset.sum_Icc_succ_top (by omega)]
    have d := doubleP n (k+1)
    push_cast at d ih ⊢
    linear_combination 3*d+ih



-- The protected prefix length, window length and first two-way sum, starting at row 3.
private def smallRows : List (ℕ × ℕ × ℕ) :=
  [(0,5,19), (0,8,90), (0,9,162), (0,10,299),
   (0,11,509), (0,12,816), (0,13,1248), (0,14,1837),
   (3,12,2619), (4,12,3634), (6,12,4926), (7,12,6543),
   (8,12,8537), (9,12,10964), (10,12,13884), (12,11,17361),
   (13,11,21463), (14,11,26262), (15,11,31834), (16,11,38259),
   (17,11,45621), (18,11,54008)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checkRows : ∀ i : Fin 22,
    smallCert (i.val+3) (smallRows[i.val]!).1 (smallRows[i.val]!).2.1 (smallRows[i.val]!).2.2 = true := by
  decide +kernel

private theorem small_value (i : Fin 22) : a (i.val+3) = (smallRows[i.val]!).2.2 :=
  small_result (checkRows i)

-- At n = t + 25, twice each window sum has the same cubic contribution per term.
-- The remaining quadratic in t depends only on the first two moments of its indices.
private def key0 (r : Finset ℕ) := ∑ i ∈ r, (853*i+23*i^2)
private def key1 (r : Finset ℕ) := ∑ i ∈ r, (83*i+i^2)
private def key2 (r : Finset ℕ) := ∑ i ∈ r, 2*i
private def level (t : ℕ) (r : Finset ℕ) := key0 r + key1 r*t + key2 r*t^2

private theorem shiftP (t i : ℕ) :
    2*P (t+25) (t+19+i) = 2*P (t+25) (t+19) + (853*i + 23*i^2)
      + (83*i+i^2)*t + 2*i*t^2 := by
  have h := doubleP (t+25) (t+19+i)
  have b := doubleP (t+25) (t+19)
  rw [show t+25-2=t+23 by omega] at h b
  push_cast at h b
  zify
  linarith only [h,b]

private theorem shiftSum (t : ℕ) (r : Finset ℕ) :
    2*(∑ i ∈ r, P (t+25) (t+19+i)) = r.card*(2*P (t+25) (t+19)) + level t r := by
  induction r using Finset.induction_on with
  | empty => simp [level,key0,key1,key2]
  | @insert j r hj ih =>
    simp only [Finset.sum_insert hj, Finset.card_insert_of_notMem hj, level, key0, key1, key2] at *
    rw [Nat.mul_add, shiftP, ih]
    ring

-- Of the 462 windows, 24 can reach or precede Corneth’s candidate at t = 0.
-- Their order persists because the linear and quadratic coefficients respect it.
private def allWin := windows 11 6
private def topWin : Finset ℕ := {1,2,3,6,7,8}
private def lowWin := allWin.filter (fun r => key0 r ≤ key0 topWin)

private theorem top_mem : topWin ∈ lowWin := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem high_cert : ∀ r ∈ allWin, key0 topWin < key0 r →
    key1 topWin ≤ key1 r ∧ key2 topWin ≤ key2 r := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem low_cert : ∀ r ∈ lowWin, ∀ s ∈ lowWin, key0 r ≤ key0 s →
    key1 r ≤ key1 s ∧ key2 r ≤ key2 s := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fiber_cert :
    (lowWin.filter (fun s => key0 s = key0 topWin)).card = 2 ∧
    ∀ r ∈ lowWin, key0 r < key0 topWin → (lowWin.filter (fun s => key0 s = key0 r)).card ≠ 2 := by decide +kernel

private theorem level_strict {t : ℕ} {s r : Finset ℕ} (h : key0 s < key0 r)
    (h1 : key1 s ≤ key1 r) (h2 : key2 s ≤ key2 r) : level t s < level t r := by
  unfold level
  have := Nat.mul_le_mul_right t h1
  have := Nat.mul_le_mul_right (t^2) h2
  omega

private theorem level_cmp {t : ℕ} {s r : Finset ℕ} (hs : s ∈ lowWin) (hr : r ∈ lowWin)
    (h : key0 s ≤ key0 r) : level t s ≤ level t r := by
  obtain ⟨a,b⟩ := low_cert s hs r hr h
  exact Nat.add_le_add (Nat.add_le_add h (Nat.mul_le_mul_right t a)) (Nat.mul_le_mul_right _ b)

private theorem low_iff {t : ℕ} {r : Finset ℕ} (h : r ∈ allWin) :
    r ∈ lowWin ↔ level t r ≤ level t topWin := by
  constructor
  · intro hr
    exact level_cmp hr top_mem (Finset.mem_filter.mp hr).2
  · intro hr
    apply Finset.mem_filter.mpr
    refine ⟨h,?_⟩
    by_contra! hbad
    obtain ⟨h1,h2⟩ := high_cert _ h hbad
    exact hr.not_gt (level_strict hbad h1 h2)

private theorem compare_score (t : ℕ) {r s : Finset ℕ} (hr : r ∈ allWin) (hs : s ∈ allWin) :
    (score (t+25) (t+19) r ≤ score (t+25) (t+19) s ↔ level t r ≤ level t s) := by
  have cr : r.card = 6 := (Finset.mem_powersetCard.mp hr).2
  have cs : s.card = 6 := (Finset.mem_powersetCard.mp hs).2
  have a := shiftSum t r
  have b := shiftSum t s
  rw [cr] at a
  rw [cs] at b
  unfold score
  omega

private theorem equal_level {t : ℕ} {r s : Finset ℕ} (hr : r ∈ lowWin) (hs : s ∈ lowWin) :
    level t r = level t s ↔ key0 r = key0 s := by
  constructor
  · intro eq
    rcases lt_trichotomy (key0 r) (key0 s) with h | h | h
    · obtain ⟨h1,h2⟩ := low_cert _ hr _ hs h.le
      exact False.elim ((level_strict (t:=t) h h1 h2).ne eq)
    · exact h
    · obtain ⟨h1,h2⟩ := low_cert _ hs _ hr h.le
      exact False.elim ((level_strict (t:=t) h h1 h2).ne eq.symm)
  · intro eq
    exact le_antisymm (level_cmp hr hs eq.le) (level_cmp hs hr eq.ge)

private theorem fiber (t : ℕ) {r : Finset ℕ} (hr : r ∈ lowWin) :
    allWin.filter (fun s => score (t+25) (t+19) s = score (t+25) (t+19) r) =
    lowWin.filter (fun s => key0 s = key0 r) := by
  have har := (Finset.mem_filter.mp hr).1
  ext s
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hs,e⟩
    have l := le_antisymm ((compare_score t hs har).mp e.le) ((compare_score t har hs).mp e.ge)
    have hsl := (low_iff (t:=t) hs).mpr (l ▸ (low_iff har).mp hr)
    exact ⟨hsl,(equal_level hsl hr).mp l⟩
  · rintro ⟨hs,e⟩
    have has := (Finset.mem_filter.mp hs).1
    have l := (equal_level (t:=t) hs hr).mpr e
    exact ⟨has,le_antisymm ((compare_score t has har).mpr l.le) ((compare_score t har has).mpr l.ge)⟩


private def valuePoly (x : ℤ) := x^4-2*x^3+38*x^2-85*x+72
private def topValue (t : ℕ) := score (t+25) (t+19) topWin

private theorem top_value (t : ℕ) : 6 * (topValue t : ℤ) = valuePoly (t+25) := by
  have H := partialSum (t+25) (t+19)
  have S := shiftSum t topWin
  have J := doubleP (t+25) (t+19)
  rw [show t+25-2=t+23 by omega] at H J
  have V : topWin.card = 6 ∧ key0 topWin = 853*27+23*163 ∧
      key1 topWin = 83*27+163 ∧ key2 topWin = 54 := by decide +kernel
  obtain ⟨c,k,l,h⟩ := V
  simp only [level,c,k,l,h] at S
  unfold topValue score valuePoly
  zify at S
  push_cast at H J S ⊢
  linear_combination H+3*S+18*J

private theorem large_cover (t : ℕ) :
    ∀ s : Finset ℕ, s.card = t+25 → (∀ j ∈ s, 0 < j) → weight (t+25) s ≤ topValue t →
      seg (t+19) ⊆ s ∧ s ⊆ seg (t+19+11) := by
  have Q := top_value t
  have B := partialSum (t+25) (t+25)
  change 6*(base (t+25):ℤ) = _ at B
  have L := doubleP (t+25) (t+19)
  have R := doubleP (t+25) (t+25+1)
  have M := doubleP (t+25) (t+25)
  have H := doubleP (t+25) (t+19+11+1)
  rw [show t+25-2=t+23 by omega] at B L R M H
  unfold valuePoly at Q
  push_cast at B L R M H Q
  apply cover_of_bounds (by omega) (by omega)
  · right
    zify
    nlinarith [sq_nonneg (t:ℤ)]
  · zify
    nlinarith [sq_nonneg (t:ℤ)]

private theorem large_result (t : ℕ) : a (t+25) = topValue t := by
  let sc := score (t+25) (t+19)
  have hc (m) (hm : m ≤ topValue t) : ways (t+25) m = (allWin.filter (fun s => sc s = m)).card := by
    rw [window_count (by omega) (large_cover t) _ hm]
    simp [allWin,sc,show t+25-(t+19)=6 by omega]
  apply IsLeast.csInf_eq
  constructor
  · change ways (t+25) (topValue t) = 2
    rw [hc _ le_rfl]
    change (allWin.filter (fun s => score (t+25) (t+19) s = score (t+25) (t+19) topWin)).card = 2
    rw [fiber t top_mem]
    exact fiber_cert.1
  · intro m he
    change ways (t+25) m = 2 at he
    by_contra! h
    rw [hc _ h.le] at he
    obtain ⟨r,hr⟩ := Finset.card_pos.mp (show 0 < (allWin.filter (fun s => sc s = m)).card by omega)
    obtain ⟨hr,erm⟩ := Finset.mem_filter.mp hr
    have ht := (Finset.mem_filter.mp top_mem).1
    have hrlt : level t r < level t topWin := lt_of_not_ge (fun h' =>
      (not_le_of_gt h) ((compare_score t ht hr).mpr h' |>.trans erm.le))
    have hl := (low_iff hr).mpr hrlt.le
    have hk : key0 r < key0 topWin := lt_of_not_ge (fun h' => hrlt.not_ge (level_cmp top_mem hl h'))
    rw [← erm] at he
    change (allWin.filter (fun s => score (t+25) (t+19) s = score (t+25) (t+19) r)).card = 2 at he
    rw [fiber t hl] at he
    exact fiber_cert.2 r hl hk he

open PowerSeries

private theorem closed (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℚ) = ((n:ℚ)^4-2*n^3+38*n^2-85*n+72)/6 := by
  have h : 6*(a n : ℤ) = valuePoly n := by
    by_cases hh : 25 ≤ n
    · obtain ⟨t,rfl⟩ : ∃ t, n=t+25 := ⟨n-25,by omega⟩
      rw [large_result]
      simpa using top_value t
    · let i : Fin 20 := ⟨n-5,by omega⟩
      let j : Fin 22 := ⟨i.val+2,by omega⟩
      have e : n = j.val+3 := by dsimp [j,i]; omega
      have finite : ∀ k : Fin 20, 6*((smallRows[k.val+2]!).2.2 : ℤ) = valuePoly ((k:ℤ)+5) := by decide +kernel
      have hf := finite i
      have ev := small_value j
      rw [← e] at ev
      rw [ev]
      change 6*((smallRows[i.val+2]!).2.2:ℤ) = valuePoly n
      rw [hf]
      congr 1
      dsimp [i]; omega
  unfold valuePoly at h
  apply (eq_div_iff (by norm_num)).mpr
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  linarith only [hq]

end Polygonal

namespace PolygonalSeries
open PowerSeries

private theorem of_quartic (a : ℕ → ℚ) (h3 : a 3 = 19) (h4 : a 4 = 90)
    (hpoly : ∀ n : ℕ, 5 ≤ n → a n =
      ((n : ℚ)^4 - 2*n^3 + 38*n^2 - 85*n + 72)/6) :
    PowerSeries.mk (fun n => if n < 3 then (0 : ℚ) else a n) * (1-X)^5 =
      X^3*(19-5*X-98*X^2+199*X^3-171*X^4+72*X^5-12*X^6) := by
  let A := PowerSeries.mk (fun n => if n < 3 then (0 : ℚ) else a n)
  change A*(1-X)^5 = _
  have hL : A*(1-X)^5 = A - C ((5 : ℕ) : ℚ)*(A*X^1) + C ((10 : ℕ) : ℚ)*(A*X^2) - C ((10 : ℕ) : ℚ)*(A*X^3) +
      C ((5 : ℕ) : ℚ)*(A*X^4) - A*X^5 := by simp only [map_natCast]; ring
  have hR : (X^3*(19-5*X-98*X^2+199*X^3-171*X^4+72*X^5-12*X^6) : PowerSeries ℚ) =
      C ((19 : ℕ) : ℚ)*X^3 - C ((5 : ℕ) : ℚ)*X^4 - C ((98 : ℕ) : ℚ)*X^5 + C ((199 : ℕ) : ℚ)*X^6 - C ((171 : ℕ) : ℚ)*X^7 + C ((72 : ℕ) : ℚ)*X^8 - C ((12 : ℕ) : ℚ)*X^9 := by
    simp only [map_natCast]; ring
  rw [hL,hR]
  ext k
  simp only [map_add,map_sub,coeff_C_mul_X_pow]
  simp only [coeff_C_mul,coeff_mul_X_pow',A,coeff_mk]
  by_cases hk : k ≤ 9
  · interval_cases k <;> norm_num [h3,h4,hpoly]
  · simp (disch := omega) only [if_pos,if_neg,hpoly]
    push_cast [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub (show 2 ≤ k by omega),
      Nat.cast_sub (show 3 ≤ k by omega), Nat.cast_sub (show 4 ≤ k by omega),
      Nat.cast_sub (show 5 ≤ k by omega)]
    ring
end PolygonalSeries

open OMA.S_oeis_a377729 in
theorem OMA.solution : type_of% @OMA.S_oeis_a377729.main := by
  refine ⟨Polygonal.closed, PolygonalSeries.of_quartic (fun n => (a n : ℚ)) ?_ ?_ Polygonal.closed⟩
  · exact_mod_cast (Polygonal.small_value 0 : OMA.S_oeis_a377729.a 3 = 19)
  · exact_mod_cast (Polygonal.small_value 1 : OMA.S_oeis_a377729.a 4 = 90)
