import OMAStatements.S_mo_501259

-- Problem: Sums of distinct powers of 3, 4 and 7
-- Credit: @sobrien032

/-!
Burr, Erdős, Graham and W. Wen-Ching Li identified 581 as the last omitted sum
in Complete sequences of sets of integer powers, Acta Arithmetica 77 (1996),
page 137. G. Melfi asked for the derivation on MathOverflow, question 501259.

The finite subset sums give a starting interval [582, 4460]. Let A, B, C be
the next unused powers of 3, 4, 7, respectively. The total of all preceding
powers is (3A + 2B + C − 24)/6 by the three geometric sums. Adjoining the
least of A, B, C extends the interval if the old interval and its translate
overlap or touch. The required gap is certified below using the spacing of
squares and two finite tables of residues modulo 134215680.
-/

namespace Mo501259Proof
open OMA.S_mo_501259

def seedPairs : List (ℕ × ℕ) :=
  [(3, 1),(4, 1),(7, 1),(3, 2),(4, 2),(3, 3),(7, 2),(4, 3),
   (3, 4),(3, 5),(4, 4),(7, 3),(3, 6),(4, 5),(3, 7)]

def seedWeights : List ℕ := seedPairs.map (fun p => p.1 ^ p.2)

/- Bit n records whether a subset sums to n. A shift adds the new power once. -/
def seedBits : List ℕ → ℕ
  | [] => 1
  | x :: xs => let b := seedBits xs; b ||| (b <<< x)

lemma mem_weights_of_le {x : ℕ} (hx : x ∈ Pow347) (hbound : x ≤ 581) :
    x ∈ seedWeights := by
  obtain ⟨b, hb, i, hi, rfl⟩ := hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  have hb3 : 3 ≤ b := by omega
  have hi' : i < 6 := by
    by_contra! he
    have hlo : (3 : ℕ) ^ 6 ≤ b ^ i :=
      (Nat.pow_le_pow_left hb3 6).trans (pow_le_pow_right₀ (by omega : 1 ≤ b) he)
    norm_num at hlo
    omega
  rcases hb with rfl | rfl | rfl <;> interval_cases i <;>
    first | decide | norm_num at hbound

lemma bit_of_subset (xs : List ℕ) (s : Finset ℕ)
    (hs : ∀ y ∈ s, y ∈ xs) : (seedBits xs).testBit (s.sum id) = true := by
  induction xs generalizing s with
  | nil =>
    have h : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      simpa using hs y hy
    simp [h, seedBits]
  | cons x xs ih =>
    simp only [seedBits, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hx : x ∈ s
    · right
      have hsum := Finset.sum_erase_add s id hx
      change (s.erase x).sum id + x = s.sum id at hsum
      constructor
      · omega
      · have hdiff : s.sum id - x = (s.erase x).sum id := by omega
        rw [hdiff]
        apply ih
        intro y hy
        have hh := Finset.mem_erase.mp hy
        exact (List.mem_cons.mp (hs y hh.2)).resolve_left hh.1
    · left
      apply ih
      intro y hy
      apply (List.mem_cons.mp (hs y hy)).resolve_left
      intro he
      exact hx (he ▸ hy)

set_option maxRecDepth 20000 in
lemma not_581 : 581 ∉ SigmaPow347 := by
  rintro ⟨s, hs, _, hsum⟩
  have h := bit_of_subset seedWeights s (by
    intro x hx
    have hle : id x ≤ s.sum id := Finset.single_le_sum (fun i _ => Nat.zero_le (id i)) hx
    exact mem_weights_of_le (hs hx) (hsum ▸ hle))
  rw [hsum] at h
  have hcert : (seedBits seedWeights).testBit 581 = false := by decide
  rw [hcert] at h
  contradiction

lemma seed_witness (xs : List ℕ) (nd : xs.Nodup) (n : ℕ)
    (h : (seedBits xs).testBit n = true) :
    ∃ s : Finset ℕ, (∀ y ∈ s, y ∈ xs) ∧ s.sum id = n := by
  induction xs generalizing n with
  | nil =>
    have hn := Nat.testBit_one_eq_true_iff_self_eq_zero.mp h
    exact ⟨∅, by simp, by simp [hn]⟩
  | cons x xs ih =>
    obtain ⟨hnot, hn⟩ := List.nodup_cons.mp nd
    simp only [seedBits, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at h
    obtain h | ⟨hx, h⟩ := h
    · obtain ⟨s, hs, he⟩ := ih hn n h
      exact ⟨s, fun y hy => List.mem_cons_of_mem x (hs y hy), he⟩
    · obtain ⟨s, hs, he⟩ := ih hn (n - x) h
      have hxs : x ∉ s := fun h => hnot (hs x h)
      refine ⟨insert x s, ?_, ?_⟩
      · intro y hy
        exact List.mem_cons.mpr ((Finset.mem_insert.mp hy).imp_right (hs y))
      · rw [Finset.sum_insert hxs, he]
        change x + (n - x) = n
        omega

lemma bits_interval (b low len n : ℕ) (hl : low ≤ n) (hu : n - low < len)
    (hc : (b >>> low) % (1 <<< len) = (1 <<< len) - 1) : b.testBit n = true := by
  rw [Nat.shiftLeft_eq, Nat.one_mul] at hc
  have hb := congrArg (fun k : ℕ => k.testBit (n - low)) hc
  change ((b >>> low) % 2 ^ len).testBit (n - low) = (2 ^ len - 1).testBit (n - low) at hb
  have hindex : low + (n - low) = n := by omega
  simpa only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
    hu, decide_true, Bool.true_and, hindex] using hb

set_option maxRecDepth 20000 in
lemma seed (n : ℕ) (hl : 582 ≤ n) (hu : n ≤ 4460) :
    ∃ s : Finset ℕ, (∀ x ∈ s, x ∈ Pow347 ∧ x ≤ 2187) ∧ s.sum id = n := by
  have hb := bits_interval (seedBits seedWeights) 582 3879 n hl (by omega) (by decide)
  obtain ⟨s, hs, hsum⟩ := seed_witness seedWeights (by decide) n hb
  refine ⟨s, ?_, hsum⟩
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (hs x hx)
  have hpairs : seedPairs.all (fun p => decide
      (p.1 ∈ ({3, 4, 7} : Finset ℕ) ∧ 1 ≤ p.2 ∧ p.1 ^ p.2 ≤ 2187)) = true := by decide
  have hh := of_decide_eq_true (List.all_eq_true.mp hpairs p hp)
  exact ⟨⟨p.1, hh.1, p.2, hh.2.1, rfl⟩, hh.2.2⟩

set_option maxRecDepth 4096 in
lemma small_gap (p q r : ℕ) (hp : 8 ≤ p) (hq : 6 ≤ q) (hr : 4 ≤ r) (hsmall : q < 12) :
    6 * min (3 ^ p) (min (4 ^ q) (7 ^ r)) + 7002 ≤ 3 * 3 ^ p + 2 * 4 ^ q + 7 ^ r := by
  have hmin : min (3 ^ p) (min (4 ^ q) (7 ^ r)) ≤ 4 ^ q :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h4 : (4 : ℕ) ^ q ≤ 4194304 := by
    exact Nat.pow_le_pow_right (by decide) (show q ≤ 11 by omega)
  by_cases hp' : 15 ≤ p
  · have h3 : 14348907 ≤ (3 : ℕ) ^ p :=
      Nat.pow_le_pow_right (by decide : 0 < 3) hp'
    omega
  by_cases hr' : 9 ≤ r
  · have h7 : 40353607 ≤ (7 : ℕ) ^ r :=
      Nat.pow_le_pow_right (by decide : 0 < 7) hr'
    omega
  have cert : ∀ i : Fin 7, ∀ j : Fin 6, ∀ k : Fin 5,
      6 * min (3 ^ ((i:ℕ) + 8)) (min (4 ^ ((j:ℕ) + 6)) (7 ^ ((k:ℕ) + 4))) + 7002 ≤
      3 * 3 ^ ((i:ℕ) + 8) + 2 * 4 ^ ((j:ℕ) + 6) + 7 ^ ((k:ℕ) + 4) := by decide
  obtain ⟨i, hi⟩ : ∃ i : Fin 7, (i:ℕ) + 8=p := ⟨⟨p - 8, by omega⟩, by dsimp; omega⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin 6, (j:ℕ) + 6=q := ⟨⟨q - 6, by omega⟩, by dsimp; omega⟩
  obtain ⟨k, hk⟩ : ∃ k : Fin 5, (k:ℕ) + 4=r := ⟨⟨r - 4, by omega⟩, by dsimp; omega⟩
  simpa only [hi, hj, hk] using cert i j k

abbrev gapMod : ℕ := 134215680

/- The centered representative agrees with the actual difference throughout
   the range needed for the interval - extension argument. -/
def gapDelta (a b : ℕ) : ℤ :=
  (((a : ℤ) - b + 7002) % (gapMod : ℤ)) - 7002

lemma gapDelta_eq (a b : ℕ) (hab : a ≤ b + 7002) (hba : b ≤ a + 7002) :
    gapDelta (a % gapMod) (b % gapMod) = (a : ℤ) - b := by
  unfold gapDelta
  simp only [Int.natCast_emod]
  rw [← Int.emod_add_emod, Int.emod_sub_emod, Int.sub_emod_emod, Int.emod_add_emod]
  rw [Int.emod_eq_of_lt (by omega) (by dsimp [gapMod]; omega)]
  omega

lemma gap_period (a s d p i : ℕ)
    (h : a ^ (s + d * p) ≡ a ^ s [MOD gapMod]) :
    a ^ (s + d * (i % p)) % gapMod = a ^ (s + d * i) % gapMod := by
  apply Function.Periodic.map_mod_nat (f := fun k => a ^ (s + d * k) % gapMod) _ i
  intro k
  have hh := h.mul_right (a ^ (d * k))
  simp only [← pow_add] at hh
  change a ^ (s + d * (k + p)) ≡ a ^ (s + d * k) [MOD gapMod]
  rw [show s + d * (k + p) = s + d * p + d * k by ring]
  exact hh

/- The possible differences from a power of four when the exponents of
   three and seven are odd. The exponent of four starts at six. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma gap_three_table : ∀ (i : Fin 256) (j : Fin 8),
    let d := gapDelta (3 ^ (1 + 2 * i.val) % gapMod) (4 ^ (6 + j.val) % gapMod)
    (-3501 : ℤ) ≤ d ∧ d ≤ 2333 → (j.val = 0 ∧ d = -1909) ∨ j.val = 7 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma gap_seven_table : ∀ (k : Fin 128) (j : Fin 8),
    let e := gapDelta (7 ^ (1 + 2 * k.val) % gapMod) (4 ^ (6 + j.val) % gapMod)
    (-7002 : ℤ) ≤ e ∧ e ≤ 7002 → (j.val = 0 ∧ (e = -4089 ∨ e = -3753)) ∨ j.val = 1 := by
  decide +kernel

set_option maxRecDepth 8192 in
lemma gap_odd (p q r : ℕ) (hq : 6 ≤ q) (hp : p % 2 = 1) (hr : r % 2 = 1)
    (hl : 6 * min (3 ^ p) (min (4 ^ q) (7 ^ r)) + 7002 >
      3 * 3 ^ p + 2 * 4 ^ q + 7 ^ r) : False := by
  have hA : 3 ^ p ≤ 4 ^ q + 2333 := by omega
  have hB : 4 ^ q ≤ 3 ^ p + 3501 := by omega
  have hC : 7 ^ r ≤ 4 ^ q + 7002 := by omega
  have hD : 4 ^ q ≤ 7 ^ r + 7002 := by omega
  let i : Fin 256 := ⟨(p / 2) % 256, Nat.mod_lt _ (by decide)⟩
  let j : Fin 8 := ⟨(q - 6) % 8, Nat.mod_lt _ (by decide)⟩
  let k : Fin 128 := ⟨(r / 2) % 128, Nat.mod_lt _ (by decide)⟩
  have ha : 3 ^ (1 + 2 * i.val) % gapMod = 3 ^ p % gapMod := by
    simpa only [show 1 + 2 * (p / 2) = p by omega] using
      gap_period 3 1 2 256 (p / 2) (by decide +kernel)
  have hb : 4 ^ (6 + j.val) % gapMod = 4 ^ q % gapMod := by
    simpa only [Nat.one_mul, show 6 + (q - 6) = q by omega] using
      gap_period 4 6 1 8 (q - 6) (by decide)
  have hc : 7 ^ (1 + 2 * k.val) % gapMod = 7 ^ r % gapMod := by
    simpa only [show 1 + 2 * (r / 2) = r by omega] using
      gap_period 7 1 2 128 (r / 2) (by decide +kernel)
  have hd := gap_three_table i j
  have he := gap_seven_table k j
  dsimp only at hd he
  rw [ha, hb, gapDelta_eq _ _ (by omega) (by omega)] at hd
  rw [hc, hb, gapDelta_eq _ _ hC hD] at he
  have hd' := hd (by omega)
  have he' := he (by omega)
  omega

lemma square_gap (u q : ℕ) (hu : Odd u) (hq : 12 ≤ q) :
    u ^ 2 + 7002 < 4 ^ q ∨ 4 ^ q + 7002 < u ^ 2 := by
  have h4 : (4 : ℕ) ^ q = (2 ^ q) ^ 2 := by
    calc
      (4 : ℕ) ^ q = (2 ^ 2) ^ q := rfl
      _ = (2 ^ q) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h4]
  have h2 : 4096 ≤ (2 : ℕ) ^ q := Nat.pow_le_pow_right (by decide : 0 < 2) hq
  have hne : u ≠ 2 ^ q := by
    obtain ⟨i, hi⟩ := hu
    obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
    rw [pow_succ]
    omega
  rcases lt_or_gt_of_ne hne with hl | hg
  · left
    have hle : u ^ 2 ≤ (2 ^ q - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hz : (2 : ℕ) ^ q - 1 + 1 = 2 ^ q := by omega
    nlinarith only [hle, h2, hz, congrArg (fun t : ℕ => t ^ 2) hz]
  · right
    have hle : (2 ^ q + 1) ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith only [hle, h2]

lemma large_gap (p q r : ℕ) (hq : 12 ≤ q) :
    6 * min (3 ^ p) (min (4 ^ q) (7 ^ r)) + 7002 ≤ 3 * 3 ^ p + 2 * 4 ^ q + 7 ^ r := by
  by_contra! hl
  by_cases he : p % 2 = 0
  · have heq : (3 : ℕ) ^ p = (3 ^ (p / 2)) ^ 2 := by rw [← pow_mul]; congr 1; omega
    have h := square_gap (3 ^ (p / 2)) q (Odd.pow (by decide : Odd (3 : ℕ))) hq
    rw [← heq] at h
    omega
  by_cases he' : r % 2 = 0
  · have heq : (7 : ℕ) ^ r = (7 ^ (r / 2)) ^ 2 := by rw [← pow_mul]; congr 1; omega
    have h := square_gap (7 ^ (r / 2)) q (Odd.pow (by decide : Odd (7 : ℕ))) hq
    rw [← heq] at h
    omega
  exact gap_odd p q r (by omega) (by omega) (by omega) hl

def tailMin (p q r : ℕ) : ℕ := min (3 ^ p) (min (4 ^ q) (7 ^ r))

def tailMass (p q r : ℕ) : ℕ := 3 * 3 ^ p + 2 * 4 ^ q + 7 ^ r

/- All values in the current interval have witnesses strictly below the next power. -/
def tailCov (cut weight : ℕ) : Prop :=
  ∀ n : ℕ, 582 ≤ n → 6 * (n + 582) + 24 ≤ weight →
    ∃ s : Finset ℕ, (∀ x ∈ s, x ∈ Pow347 ∧ x < cut) ∧ s.sum id = n

set_option maxRecDepth 4096 in
lemma tail_extend (cut next weight : ℕ) (hc : cut ∈ Pow347) (hnext : cut < next)
    (hover : 6 * cut + 7002 ≤ weight) (hold : tailCov cut weight) :
    tailCov next (weight + 6 * cut) := by
  intro n hl hu
  by_cases h : 6 * (n + 582) + 24 ≤ weight
  · obtain ⟨s, hs, hsum⟩ := hold n hl h
    exact ⟨s, fun x hx => ⟨(hs x hx).1, lt_trans (hs x hx).2 hnext⟩, hsum⟩
  · obtain ⟨s, hs, hsum⟩ := hold (n - cut) (by omega) (by omega)
    have hfresh : cut ∉ s := fun hc' => (Nat.lt_irrefl cut) (hs cut hc').2
    refine ⟨insert cut s, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hc, hnext⟩
      · exact ⟨(hs x hx).1, lt_trans (hs x hx).2 hnext⟩
    · rw [Finset.sum_insert hfresh, hsum]
      simp only [id_eq]
      omega

lemma tail_pow_ne {a b i j : ℕ} (hc : a.Coprime b) (ha : 1 < a) (hi : 0 < i) :
    a ^ i ≠ b ^ j := by
  intro h
  have hcp := Nat.Coprime.pow i j hc
  rw [← h, Nat.coprime_self] at hcp
  have hbig : 1 < a ^ i := one_lt_pow₀ ha (by omega)
  omega

lemma tail_step (p q r : ℕ) (hp : 8 ≤ p) (hq : 6 ≤ q) (hr : 4 ≤ r)
    (hgap : 6 * tailMin p q r + 7002 ≤ tailMass p q r)
    (hc : tailCov (tailMin p q r) (tailMass p q r)) :
    ∃ i j k : ℕ, 8 ≤ i ∧ 6 ≤ j ∧ 4 ≤ k ∧ tailMass p q r < tailMass i j k ∧
      tailCov (tailMin i j k) (tailMass i j k) := by
  have h34 : (3 : ℕ) ^ p ≠ 4 ^ q := tail_pow_ne (by decide) (by decide) (by omega)
  have h37 : (3 : ℕ) ^ p ≠ 7 ^ r := tail_pow_ne (by decide) (by decide) (by omega)
  have h47 : (4 : ℕ) ^ q ≠ 7 ^ r := tail_pow_ne (by decide) (by decide) (by omega)
  have h3 : 0 < (3 : ℕ) ^ p := by positivity
  have h4 : 0 < (4 : ℕ) ^ q := by positivity
  have h7 : 0 < (7 : ℕ) ^ r := by positivity
  by_cases h : (3 : ℕ) ^ p < 4 ^ q ∧ (3 : ℕ) ^ p < 7 ^ r
  · have hmin : tailMin p q r = 3 ^ p := by unfold tailMin; omega
    have hlegal : (3 : ℕ) ^ p ∈ Pow347 := ⟨3, by decide, p, by omega, rfl⟩
    have hmass : tailMass (p + 1) q r = tailMass p q r + 6 * 3 ^ p := by
      simp only [tailMass, pow_succ]; omega
    refine ⟨p + 1, q, r, by omega, hq, hr, by rw [hmass]; omega, ?_⟩
    rw [hmin] at hgap hc
    rw [hmass]
    apply tail_extend _ _ _ hlegal _ hgap hc
    unfold tailMin
    rw [pow_succ]
    omega
  · by_cases h' : (4 : ℕ) ^ q < 3 ^ p ∧ (4 : ℕ) ^ q < 7 ^ r
    · have hmin : tailMin p q r = 4 ^ q := by unfold tailMin; omega
      have hlegal : (4 : ℕ) ^ q ∈ Pow347 := ⟨4, by decide, q, by omega, rfl⟩
      have hmass : tailMass p (q + 1) r = tailMass p q r + 6 * 4 ^ q := by
        simp only [tailMass, pow_succ]; omega
      refine ⟨p, q + 1, r, hp, by omega, hr, by rw [hmass]; omega, ?_⟩
      rw [hmin] at hgap hc
      rw [hmass]
      apply tail_extend _ _ _ hlegal _ hgap hc
      unfold tailMin
      rw [pow_succ]
      omega
    · have hmin : tailMin p q r = 7 ^ r := by unfold tailMin; omega
      have hlegal : (7 : ℕ) ^ r ∈ Pow347 := ⟨7, by decide, r, by omega, rfl⟩
      have hmass : tailMass p q (r + 1) = tailMass p q r + 6 * 7 ^ r := by
        simp only [tailMass, pow_succ]; omega
      refine ⟨p, q, r + 1, hp, hq, by omega, by rw [hmass]; omega, ?_⟩
      rw [hmin] at hgap hc
      rw [hmass]
      apply tail_extend _ _ _ hlegal _ hgap hc
      unfold tailMin
      rw [pow_succ]
      omega

/- Each step strictly increases the integer weight, so the covered upper bounds are unbounded. -/
lemma tail_complete
    (hseed : ∀ n : ℕ, 582 ≤ n → n ≤ 4460 →
      ∃ s : Finset ℕ, (∀ x ∈ s, x ∈ Pow347 ∧ x ≤ 2187) ∧ s.sum id = n)
    (hgap : ∀ p q r : ℕ, 8 ≤ p → 6 ≤ q → 4 ≤ r →
      6 * min (3 ^ p) (min (4 ^ q) (7 ^ r)) + 7002 ≤ 3 * 3 ^ p + 2 * 4 ^ q + 7 ^ r)
    (n : ℕ) (hn : 581 < n) : n ∈ SigmaPow347 := by
  have hstates (t : ℕ) : ∃ p q r : ℕ, 8 ≤ p ∧ 6 ≤ q ∧ 4 ≤ r ∧ t ≤ tailMass p q r ∧
      tailCov (tailMin p q r) (tailMass p q r) := by
    induction t with
    | zero =>
      refine ⟨8, 6, 4, by decide, by decide, by decide, Nat.zero_le _, ?_⟩
      intro x hx hbound
      have hm : tailMass 8 6 4 = 30276 := by decide
      have hc : tailMin 8 6 4 = 2401 := by decide
      obtain ⟨s, hs, hs'⟩ := hseed x hx (by omega)
      exact ⟨s, fun y hy => ⟨(hs y hy).1, by have := (hs y hy).2; omega⟩, hs'⟩
    | succ t ih =>
      obtain ⟨p, q, r, hp, hq, hr, ht, hc⟩ := ih
      obtain ⟨i, j, k, hi, hj, hk, hw, hc'⟩ :=
        tail_step p q r hp hq hr (hgap p q r hp hq hr) hc
      exact ⟨i, j, k, hi, hj, hk, by omega, hc'⟩
  obtain ⟨p, q, r, _, _, _, ht, hc⟩ := hstates (6 * (n + 582) + 24)
  obtain ⟨s, hs, hsum⟩ := hc n (by omega) ht
  refine ⟨s, fun x hx => (hs x hx).1, ?_, hsum⟩
  rcases s.eq_empty_or_nonempty with he | he
  · simp [he] at hsum
    omega
  · exact he

end Mo501259Proof

open Mo501259Proof

theorem OMA.solution : type_of% @OMA.S_mo_501259.main := by
  refine ⟨not_581, tail_complete seed ?_⟩
  intro p q r hp hq hr
  by_cases h : q < 12
  · exact small_gap p q r hp hq hr h
  · exact large_gap p q r (by omega)
