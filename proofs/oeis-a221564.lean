import OMAStatements.S_oeis_a221564
import Mathlib

/-!
# A221564: a(3k+1) = 2k for the FO4C3 card shuffle

For a packet of n >= 4 cards, one move sends the card at position S(p) to position p, where
S(0) = 0, S(p) = p + 3 when p + 3 < n, and S(p) = n - p otherwise, flipping the card exactly when
p = 0 or p + 3 >= n (`getElem?_move`). So after m moves, position p holds the card that started at
the position given by the m-th iterate of the signed map S on (position, face) pairs
(`val_iter`), and the packet is restored exactly when every (p, face down) is fixed by that
iterate (`iter_deck_iff`).

For n = 3k + 1 the signed map is a rotation by one step on three cycles of length 2k:
the top card (period 2), the positions 2 mod 3 (decoder `D2`), and the positions 1 and 0 mod 3
taken together (decoder `D1`, which carries an invariant face bit). Each decoder turns S into
z -> z + 1 mod 2k. So every card is back after 2k moves, and the card at position 2 is back
exactly when 2k divides m. Hence the minimal period is 2k.
-/

namespace OMA.P221564

open OMA.S_oeis_a221564

/-- After one move, the card at position p comes from position (S n (p, f)).1, with this
change of face. -/
def S (n : ℕ) (s : ℕ × Bool) : ℕ × Bool :=
  if s.1 = 0 then (0, !s.2) else if s.1 + 3 < n then (s.1 + 3, s.2) else (n - s.1, !s.2)

def val (l : List (ℕ × Bool)) (s : ℕ × Bool) : ℕ × Bool :=
  ((l.getD s.1 (0, false)).1, Bool.xor (l.getD s.1 (0, false)).2 s.2)

lemma length_move (l : List (ℕ × Bool)) (hl : 4 ≤ l.length) : (move l).length = l.length := by
  simp only [move, List.length_rotate, List.length_append, List.length_map, List.length_reverse,
    List.length_take, List.length_drop]
  omega

lemma getElem?_move (l : List (ℕ × Bool)) (hl : 4 ≤ l.length) (p : ℕ) (hp : p < l.length) :
    (move l)[p]? =
      if p = 0 then (l[0]?).map (fun c => (c.1, !c.2))
      else if p + 3 < l.length then l[p + 3]?
      else (l[l.length - p]?).map (fun c => (c.1, !c.2)) := by
  have h4 : min 4 l.length = 4 := by omega
  unfold move
  rw [List.getElem?_rotate (by simp; omega)]
  have hAB : ((l.take 4).reverse.map (fun c => (c.1, !c.2)) ++ l.drop 4).length = l.length := by
    simp; omega
  rw [hAB]
  split_ifs with h0 h3
  · subst h0
    rw [Nat.mod_eq_of_lt (by omega : 0 + 3 < l.length)]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_map,
      List.getElem?_reverse (by simp; omega)]
    simp [h4]
  · rw [Nat.mod_eq_of_lt (by omega : p + 3 < l.length)]
    rw [List.getElem?_append_right (by simp; omega)]
    simp [h4]
    congr 1
    omega
  · have hm : (p + 3) % l.length = p + 3 - l.length := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hm, List.getElem?_append_left (by simp; omega), List.getElem?_map,
      List.getElem?_reverse (by simp; omega)]
    simp [h4]
    rw [List.getElem?_take, if_pos (by omega)]
    congr 2
    omega

lemma val_move (l : List (ℕ × Bool)) (hl : 4 ≤ l.length) (s : ℕ × Bool) (hs : s.1 < l.length) :
    val (move l) s = val l (S l.length s) := by
  obtain ⟨p, f⟩ := s
  simp only at hs
  unfold val S
  simp only [List.getD_eq_getElem?_getD]
  rw [getElem?_move l hl p hs]
  split_ifs with h0 h3
  · rw [List.getElem?_eq_getElem (by omega : 0 < l.length)]
    simp
  · rw [List.getElem?_eq_getElem (by omega : p + 3 < l.length)]
  · rw [List.getElem?_eq_getElem (by omega : l.length - p < l.length)]
    simp

lemma S_lt (n : ℕ) (s : ℕ × Bool) (hs : s.1 < n) : (S n s).1 < n := by
  unfold S
  split_ifs <;> simp <;> omega

lemma iter_lt (n : ℕ) (m : ℕ) : ∀ s : ℕ × Bool, s.1 < n → ((S n)^[m] s).1 < n := by
  induction m with
  | zero => intro s hs; simpa using hs
  | succ m ih =>
    intro s hs
    rw [Function.iterate_succ_apply']
    exact S_lt n _ (ih s hs)

lemma length_iter (m : ℕ) : ∀ l : List (ℕ × Bool), 4 ≤ l.length →
    (move^[m] l).length = l.length := by
  induction m with
  | zero => intro l hl; rfl
  | succ m ih =>
    intro l hl
    rw [Function.iterate_succ_apply, ih (move l) (by rw [length_move l hl]; exact hl),
      length_move l hl]

lemma val_iter (n : ℕ) (hn : 4 ≤ n) (m : ℕ) : ∀ l : List (ℕ × Bool), l.length = n →
    ∀ s : ℕ × Bool, s.1 < n → val (move^[m] l) s = val l ((S n)^[m] s) := by
  induction m with
  | zero => intro l hl s hs; rfl
  | succ m ih =>
    intro l hl s hs
    rw [Function.iterate_succ_apply, ih (move l) (by rw [length_move l (by omega), hl]) s hs,
      Function.iterate_succ_apply']
    have h := iter_lt n m s hs
    rw [val_move l (by omega) _ (by rw [hl]; exact h), hl]

lemma length_deck (n : ℕ) : (deck n).length = n := by
  simp [deck]

lemma val_deck (n : ℕ) (s : ℕ × Bool) (hs : s.1 < n) : val (deck n) s = s := by
  obtain ⟨p, f⟩ := s
  simp only at hs
  unfold val deck
  simp [List.getD_eq_getElem?_getD, hs]

lemma val_false (l : List (ℕ × Bool)) (p : ℕ) (hp : p < l.length) : val l (p, false) = l[p] := by
  unfold val
  simp [List.getD_eq_getElem?_getD, hp]

lemma iter_deck_iff (n : ℕ) (hn : 4 ≤ n) (m : ℕ) :
    move^[m] (deck n) = deck n ↔ ∀ p < n, (S n)^[m] (p, false) = (p, false) := by
  constructor
  · intro h p hp
    have h1 := val_iter n hn m (deck n) (length_deck n) (p, false) hp
    rw [h, val_deck n (p, false) hp, val_deck n _ (iter_lt n m (p, false) hp)] at h1
    exact h1.symm
  · intro h
    have hlen : (move^[m] (deck n)).length = n := by
      rw [length_iter m (deck n) (by rw [length_deck]; exact hn), length_deck]
    apply List.ext_getElem (by rw [hlen, length_deck])
    intro p hp1 hp2
    rw [hlen] at hp1
    rw [← val_false _ p (by rw [hlen]; exact hp1), ← val_false _ p hp2,
      val_iter n hn m (deck n) (length_deck n) (p, false) hp1, h p hp1]

/-- Decoder for the cycle of the positions 2 mod 3. -/
def D2 (k z : ℕ) : ℕ × Bool := if z < k then (3 * z + 2, false) else (3 * (z - k) + 2, true)

/-- Decoder for the cycle of the positions 1 and 0 mod 3 (other than 0). -/
def D1 (k : ℕ) (I : Bool) (z : ℕ) : ℕ × Bool :=
  if z < k then (3 * z + 1, I) else (3 * (z - k) + 3, !I)

lemma S_D2 (k : ℕ) (hk : 1 ≤ k) (z : ℕ) (hz : z < 2 * k) :
    S (3 * k + 1) (D2 k z) = D2 k ((z + 1) % (2 * k)) := by
  rcases Nat.lt_or_ge (z + 1) (2 * k) with h | h
  · rw [Nat.mod_eq_of_lt h]
    unfold S D2
    split_ifs <;> simp_all <;> omega
  · have hz' : z + 1 = 2 * k := by omega
    rw [hz', Nat.mod_self]
    unfold S D2
    split_ifs <;> simp_all <;> omega

lemma S_D1 (k : ℕ) (hk : 1 ≤ k) (I : Bool) (z : ℕ) (hz : z < 2 * k) :
    S (3 * k + 1) (D1 k I z) = D1 k I ((z + 1) % (2 * k)) := by
  rcases Nat.lt_or_ge (z + 1) (2 * k) with h | h
  · rw [Nat.mod_eq_of_lt h]
    unfold S D1
    split_ifs <;> simp_all <;> omega
  · have hz' : z + 1 = 2 * k := by omega
    rw [hz', Nat.mod_self]
    unfold S D1
    split_ifs <;> simp_all <;> omega

lemma iter_D2 (k : ℕ) (hk : 1 ≤ k) (m : ℕ) : ∀ z, z < 2 * k →
    (S (3 * k + 1))^[m] (D2 k z) = D2 k ((z + m) % (2 * k)) := by
  induction m with
  | zero => intro z hz; rw [Function.iterate_zero_apply, Nat.add_zero, Nat.mod_eq_of_lt hz]
  | succ m ih =>
    intro z hz
    rw [Function.iterate_succ_apply', ih z hz, S_D2 k hk _ (Nat.mod_lt _ (by omega)),
      Nat.mod_add_mod, Nat.add_assoc]

lemma iter_D1 (k : ℕ) (hk : 1 ≤ k) (I : Bool) (m : ℕ) : ∀ z, z < 2 * k →
    (S (3 * k + 1))^[m] (D1 k I z) = D1 k I ((z + m) % (2 * k)) := by
  induction m with
  | zero => intro z hz; rw [Function.iterate_zero_apply, Nat.add_zero, Nat.mod_eq_of_lt hz]
  | succ m ih =>
    intro z hz
    rw [Function.iterate_succ_apply', ih z hz, S_D1 k hk I _ (Nat.mod_lt _ (by omega)),
      Nat.mod_add_mod, Nat.add_assoc]

/-- Every card comes back after 2k moves, face down. -/
lemma per_all (k : ℕ) (hk : 1 ≤ k) (p : ℕ) (hp : p < 3 * k + 1) :
    (S (3 * k + 1))^[2 * k] (p, false) = (p, false) := by
  have hback : ∀ z, z < 2 * k → (z + 2 * k) % (2 * k) = z := by
    intro z hz
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hz]
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0
    have h2 : (S (3 * k + 1))^[2] (0, false) = (0, false) := by
      simp [S]
    rw [Function.iterate_mul]
    exact Function.iterate_fixed h2 k
  · have h3 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h3 with h3 | h3 | h3
    · have hd : (p, false) = D1 k true (p / 3 - 1 + k) := by
        unfold D1
        rw [if_neg (by omega)]
        simp only [Bool.not_true, Prod.mk.injEq, and_true]
        omega
      rw [hd, iter_D1 k hk true _ _ (by omega), hback _ (by omega)]
    · have hd : (p, false) = D1 k false (p / 3) := by
        unfold D1
        rw [if_pos (by omega)]
        simp only [Prod.mk.injEq, and_true]
        omega
      rw [hd, iter_D1 k hk false _ _ (by omega), hback _ (by omega)]
    · have hd : (p, false) = D2 k (p / 3) := by
        unfold D2
        rw [if_pos (by omega)]
        simp only [Prod.mk.injEq, and_true]
        omega
      rw [hd, iter_D2 k hk _ _ (by omega), hback _ (by omega)]

theorem sol : type_of% @OMA.S_oeis_a221564.main := by
  intro k hk
  have hn : 4 ≤ 3 * k + 1 := by omega
  have hper : ∀ m, Function.IsPeriodicPt move m (deck (3 * k + 1)) ↔ 2 * k ∣ m := by
    intro m
    unfold Function.IsPeriodicPt Function.IsFixedPt
    rw [iter_deck_iff _ hn]
    constructor
    · intro h
      have h2 := h 2 (by omega)
      have hd : ((2 : ℕ), false) = D2 k 0 := by
        unfold D2
        rw [if_pos (by omega)]
      rw [hd, iter_D2 k hk m 0 (by omega)] at h2
      apply Nat.dvd_of_mod_eq_zero
      have hlt := Nat.mod_lt m (by omega : 0 < 2 * k)
      rw [Nat.zero_add] at h2
      clear h hd
      unfold D2 at h2
      rw [if_pos (by omega : 0 < k)] at h2
      by_cases hc : m % (2 * k) < k
      · rw [if_pos hc] at h2
        simp only [Prod.mk.injEq] at h2
        omega
      · rw [if_neg hc] at h2
        simp at h2
    · rintro ⟨j, rfl⟩ p hp
      rw [Function.iterate_mul]
      exact Function.iterate_fixed (per_all k hk p hp) j
  unfold a
  apply Nat.dvd_antisymm
  · exact Function.IsPeriodicPt.minimalPeriod_dvd ((hper _).2 dvd_rfl)
  · exact (hper _).1 (Function.isPeriodicPt_minimalPeriod move _)

end OMA.P221564

theorem OMA.solution : type_of% @OMA.S_oeis_a221564.main := OMA.P221564.sol
