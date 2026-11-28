import OMAStatements.S_oeis_a001969

-- Problem: A001969 (Ratushnyak's conjecture): n has an even number of ones in binary iff n is
--   rotr(x) XOR rotl(x) for some x, both one-place rotations taken within the binary width of x.
-- Credit: @alan-phobos-claude
-- Proof: each bit of x lands in two places of rotr(x) XOR rotl(x), so the ones there come in pairs
--   (mod 2). Conversely, take an odd width w with n < 2^w. Stepping by 2 around a cycle of odd length
--   visits every position, so the bits of x can be filled in along that walk, each step fixing one
--   bit of n. The walk closes up exactly because n has an even number of ones. Of x and its
--   complement (same image), take the one whose top bit is set, so that its width is w.

open OMA.S_oeis_a001969 Finset

namespace A001969

/-- The number whose bits below `k` are `f 0, f 1, …, f (k-1)`. -/
def ofBits (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (f 0).toNat + 2 * ofBits (fun i => f (i + 1)) k

lemma testBit_ofBits (f : ℕ → Bool) (k i : ℕ) :
    (ofBits f k).testBit i = (decide (i < k) && f i) := by
  induction k generalizing f i with
  | zero => simp [ofBits]
  | succ k ih =>
    cases i with
    | zero => rw [Nat.testBit_zero]; cases h : f 0 <;> simp [ofBits, h]
    | succ i =>
      rw [Nat.testBit_succ, ofBits, show ((f 0).toNat + 2 * ofBits (fun i => f (i + 1)) k) / 2 =
        ofBits (fun i => f (i + 1)) k by cases f 0 <;> simp <;> omega, ih]
      simp

lemma xor_toNat (a b : Bool) : (a ^^ b).toNat + (a && b).toNat + (a && b).toNat = a.toNat + b.toNat := by
  cases a <;> cases b <;> rfl

/-- Bits of `n` summed below `a` or below `b` agree once `n < 2 ^ a` and `n < 2 ^ b`. -/
lemma sum_bits {n a b : ℕ} (ha : n < 2 ^ a) (hb : n < 2 ^ b) :
    ∑ i ∈ range a, (n.testBit i).toNat = ∑ i ∈ range b, (n.testBit i).toNat := by
  rcases le_total a b with h | h
  · refine sum_subset (range_subset_range.2 h) fun i _ hi => ?_
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by simpa using hi)))]; rfl
  · refine (sum_subset (range_subset_range.2 h) fun i _ hi => ?_).symm
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by simpa using hi)))]; rfl

lemma ones_eq {n w : ℕ} (h : n < 2 ^ w) : ones n = ∑ i ∈ range w, (n.testBit i).toNat :=
  sum_bits Nat.lt_log2_self h


/-- Odd width `w`: step `s` of the walk `0, 2, 4, …` (mod `w`) reads bit `idx w s` of the target. -/
def idx (w s : ℕ) : ℕ := if 2 * s + 1 < w then 2 * s + 1 else 2 * s + 1 - w

/-- The bits of the preimage along the walk: start at `c`, flip by each bit read. -/
def chain (N : ℕ → Bool) (w : ℕ) (c : Bool) : ℕ → Bool
  | 0 => c
  | s + 1 => chain N w c s ^^ N (idx w s)

/-- Position `p` is reached at step `tau w p` of the walk. -/
def tau (w p : ℕ) : ℕ := if p % 2 = 0 then p / 2 else (p + w) / 2

lemma chain_parity (N : ℕ → Bool) (w : ℕ) (c : Bool) (t : ℕ) :
    (chain N w c t).toNat % 2 = (c.toNat + ∑ s ∈ range t, (N (idx w s)).toNat) % 2 := by
  induction t with
  | zero => simp [chain]
  | succ t ih =>
    rw [chain, sum_range_succ]
    have := xor_toNat (chain N w c t) (N (idx w t))
    omega

lemma chain_xor (N : ℕ → Bool) (w : ℕ) (c : Bool) (t : ℕ) : chain N w c t = (c ^^ chain N w false t) := by
  induction t with
  | zero => simp [chain]
  | succ t ih => rw [chain, chain, ih, Bool.xor_assoc]

/-- The walk reads every bit below the odd width exactly once. -/
lemma sum_idx (N : ℕ → Bool) {w r : ℕ} (hw : w = 2 * r + 1) :
    ∑ s ∈ range w, (N (idx w s)).toNat = ∑ j ∈ range w, (N j).toNat := by
  subst hw
  refine sum_nbij (idx (2 * r + 1)) (fun s hs => ?_) (fun s hs s' hs' h => ?_) (fun j hj => ?_) (fun _ _ => rfl)
  · simp only [mem_range, idx] at *; split_ifs <;> omega
  · simp only [coe_range, Set.mem_Iio, idx] at *; split_ifs at h <;> omega
  · rw [mem_coe, mem_range] at hj
    refine ⟨if j % 2 = 1 then j / 2 else (j + 2 * r + 1) / 2, ?_, ?_⟩
    · rw [mem_coe, mem_range]; split_ifs <;> omega
    · simp only [idx]; split_ifs <;> omega

/-- The two neighbours of bit `i` under the rotations, as positions below `w = 2r+1`. -/
lemma walk_step {w r i : ℕ} (hw : w = 2 * r + 1) (hr : 1 ≤ r) (hi : i < w) :
    let rl := if i < 1 then w - 1 + i else i - 1
    let rr := if i < w - 1 then 1 + i else i - (w - 1)
    tau w rl < w ∧ idx w (tau w rl) = i ∧
      (tau w rr = tau w rl + 1 ∨ (tau w rr = 0 ∧ tau w rl + 1 = w)) := by
  simp only [tau, idx]; split_ifs <;> omega

/-- Rotating a word by one place in either direction keeps its number of ones. -/
lemma even_rot (w : ℕ) (hw : 1 ≤ w) (v : BitVec w) :
    Even (∑ i ∈ range w, ((v.rotateRight 1 ^^^ v.rotateLeft 1).getLsbD i).toNat) := by
  obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
  rcases m with _ | m
  · simp [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft]
  have h1 : 1 % (m + 1 + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  have hr : ∑ i ∈ range (m + 1 + 1), ((v.rotateRight 1).getLsbD i).toNat =
      ∑ i ∈ range (m + 1 + 1), (v.getLsbD i).toNat := by
    rw [sum_range_succ, sum_range_succ' (fun i => (v.getLsbD i).toNat)]
    congr 1
    · refine sum_congr rfl fun i hi => ?_
      rw [mem_range] at hi
      simp [BitVec.getLsbD_rotateRight, h1, hi, Nat.add_comm 1 i]
    · simp [h1]
  have hl : ∑ i ∈ range (m + 1 + 1), ((v.rotateLeft 1).getLsbD i).toNat =
      ∑ i ∈ range (m + 1 + 1), (v.getLsbD i).toNat := by
    rw [sum_range_succ' (fun i => ((v.rotateLeft 1).getLsbD i).toNat), sum_range_succ (fun i => (v.getLsbD i).toNat)]
    congr 1
    · refine sum_congr rfl fun i hi => ?_
      rw [mem_range] at hi
      simp [h1, hi, BitVec.getLsbD_eq_getElem (show i < m + 1 + 1 by omega)]
    · simp [h1]
  have hsum := sum_congr rfl (fun i (_ : i ∈ range (m + 1 + 1)) =>
    xor_toNat ((v.rotateRight 1).getLsbD i) ((v.rotateLeft 1).getLsbD i))
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, hr, hl] at hsum
  simp only [BitVec.getLsbD_xor]
  exact Nat.even_iff.2 (by omega)

lemma even_ones (x : ℕ) : Even (ones (rotatedXor x)) := by
  have h : ones (rotatedXor x) = ∑ i ∈ range (width x),
      (((BitVec.ofNat (width x) x).rotateRight 1 ^^^ (BitVec.ofNat (width x) x).rotateLeft 1).getLsbD i).toNat :=
    ones_eq (BitVec.isLt _)
  rw [h]; exact even_rot _ (by simp [width]) _

lemma surj (n : ℕ) (hev : Even (ones n)) : ∃ x, rotatedXor x = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by unfold rotatedXor width; rw [Nat.log2_zero]; decide⟩
  have hL : n < 2 ^ width n := Nat.lt_log2_self
  obtain ⟨r, w, hwr, hw⟩ : ∃ r w, w = 2 * r + 1 ∧ n < 2 ^ w :=
    ⟨width n / 2, _, rfl, lt_of_lt_of_le hL (Nat.pow_le_pow_right (by decide) (by omega))⟩
  have hr : 1 ≤ r := by
    by_contra h0
    obtain rfl : n = 1 := by
      have : n < 2 ^ 1 := by rwa [hwr, show r = 0 by omega] at hw
      omega
    rw [ones_eq (show (1 : ℕ) < 2 ^ 1 by decide)] at hev
    exact absurd hev (by decide)
  have h1w : 1 % w = 1 := Nat.mod_eq_of_lt (by omega)
  -- the walk closes up because `n` has an even number of ones
  have hclose : ∀ c, chain n.testBit w c w = c := by
    intro c
    have hp := chain_parity n.testBit w c w
    rw [sum_idx _ hwr, ← ones_eq hw] at hp
    have he := Nat.even_iff.1 hev
    cases c <;> cases h : chain n.testBit w _ w <;> simp_all <;> omega
  obtain ⟨c, hc⟩ : ∃ c, chain n.testBit w c r = true :=
    ⟨!chain n.testBit w false r, by rw [chain_xor]; cases chain n.testBit w false r <;> rfl⟩
  have hbit := testBit_ofBits (fun p => chain n.testBit w c (tau w p)) w
  set x := ofBits (fun p => chain n.testBit w c (tau w p)) w
  have htop : x.testBit (w - 1) = true := by
    rw [hbit]; simp only [tau]; rw [if_pos (by omega), show (w - 1) / 2 = r by omega]; simp [hc]; omega
  have hlt : x < 2 ^ w := Nat.lt_pow_two_of_testBit x (fun i hi => by rw [hbit]; simp; omega)
  have hge : 2 ^ (w - 1) ≤ x := Nat.ge_two_pow_of_testBit htop
  have hwidth : width x = w := by
    have hx0 : x ≠ 0 := by have := Nat.one_le_two_pow (n := w - 1); omega
    unfold width; rw [(Nat.log2_eq_iff hx0).2 ⟨hge, by rwa [Nat.sub_add_cancel (by omega)]⟩]; omega
  have hv : ∀ j, j < w → (BitVec.ofNat w x).getLsbD j = chain n.testBit w c (tau w j) := fun j hj => by
    rw [BitVec.getLsbD_ofNat, hbit]; simp [hj]
  refine ⟨x, ?_⟩
  unfold rotatedXor
  rw [hwidth]
  apply Nat.eq_of_testBit_eq; intro i
  rw [BitVec.testBit_toNat, BitVec.getLsbD_xor]
  by_cases hi : i < w
  · have eR : ((BitVec.ofNat w x).rotateRight 1).getLsbD i =
        chain n.testBit w c (tau w (if i < w - 1 then 1 + i else i - (w - 1))) := by
      rw [BitVec.getLsbD_rotateRight, h1w]
      split_ifs with h
      · simp [h, hv _ (by omega : 1 + i < w)]
      · simp [h, hi, hv _ (by omega : i - (w - 1) < w)]
    have eL : ((BitVec.ofNat w x).rotateLeft 1).getLsbD i =
        chain n.testBit w c (tau w (if i < 1 then w - 1 + i else i - 1)) := by
      rw [BitVec.getLsbD_rotateLeft, h1w]
      split_ifs with h
      · simp [h, hv _ (by omega : w - 1 + i < w)]
      · simp [h, hi, hv _ (by omega : i - 1 < w)]
    rw [eR, eL]
    obtain ⟨-, hidx, hcase⟩ := walk_step hwr hr hi
    generalize tau w (if i < 1 then w - 1 + i else i - 1) = t at hidx hcase ⊢
    have hnext : chain n.testBit w c (tau w (if i < w - 1 then 1 + i else i - (w - 1))) =
        chain n.testBit w c (t + 1) := by
      rcases hcase with h | ⟨h, h'⟩
      · rw [h]
      · rw [h, h', hclose]; rfl
    rw [hnext, chain, hidx]
    cases chain n.testBit w c t <;> cases n.testBit i <;> rfl
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft, h1w, hi,
      show ¬ i < w - 1 by omega, show ¬ i < 1 by omega]

end A001969

theorem OMA.solution : type_of% @OMA.S_oeis_a001969.main :=
  fun n => ⟨A001969.surj n, fun ⟨x, hx⟩ => hx ▸ A001969.even_ones x⟩
