import OMAReductions.R_oeis_a384132_R1

/-!
# Proof of `oeis-a384132.R1.H1`

Proves `¬ IsSumOfFourDistinctCubes 121`, i.e., `121^3 = 1771561` cannot be written as
`x^3 + y^3 + z^3 + w^3` with `0 < x < y < z < w`.

Any such representation satisfies `77 ≤ w ≤ 120`, `z < w`, `y < z`, `0 < x < y`, and
`x^3 = 121^3 - w^3 - z^3 - y^3`. We exhaustively verify with `decide +kernel` that for every valid
triple `(w, z, y)`, either the remainder `rem = 121^3 - w^3 - z^3 - y^3` is `0`, `≥ y^3`, has a
residue modulo `9` outside `{0, 1, 8}`, or strictly lies between consecutive cubes `c^3 < rem < (c+1)^3`.
-/

namespace OeisA384132R1H1Proof

private def target : ℕ := 121 ^ 3

private def cbrtSearch (m lo hi : ℕ) : ℕ → ℕ
  | 0 => lo
  | fuel + 1 =>
    let mid := (lo + hi + 1) / 2
    if mid * mid * mid ≤ m then cbrtSearch m mid hi fuel
    else cbrtSearch m lo (mid - 1) fuel

private def notCubeLt (rem y3 : ℕ) : Bool :=
  if rem == 0 || y3 ≤ rem then true
  else
    let r9 := rem % 9
    if r9 != 0 && r9 != 1 && r9 != 8 then true
    else
      let c := cbrtSearch rem 0 127 7
      let c1 := c + 1
      decide (c * c * c < rem ∧ rem < c1 * c1 * c1)

private lemma cube_mod_nine (x : ℕ) : x ^ 3 % 9 = 0 ∨ x ^ 3 % 9 = 1 ∨ x ^ 3 % 9 = 8 := by
  have h : x ^ 3 % 9 = (x % 9) ^ 3 % 9 := by rw [Nat.pow_mod]
  rw [h]
  have hlt : x % 9 < 9 := Nat.mod_lt x (by decide)
  generalize x % 9 = r at hlt
  interval_cases r <;> decide

private lemma notCubeLt_sound {rem y x : ℕ} (hxpos : 0 < x) (hxy : x < y)
    (hok : notCubeLt rem (y * y * y) = true) : x ^ 3 ≠ rem := by
  intro heq
  unfold notCubeLt at hok
  by_cases h0 : rem = 0
  · have : 0 < x ^ 3 := pow_pos hxpos 3
    omega
  by_cases hge : y * y * y ≤ rem
  · have hlt : x ^ 3 < y ^ 3 := Nat.pow_lt_pow_left hxy (by decide)
    have hy3 : y ^ 3 = y * y * y := by ring
    omega
  have hcond1 : (rem == 0 || y * y * y ≤ rem) = false := by
    simp [h0, hge]
  rw [hcond1] at hok
  simp only [Bool.false_eq_true, ↓reduceIte] at hok
  have hm9 := cube_mod_nine x
  rw [heq] at hm9
  have hcond2 : (rem % 9 != 0 && rem % 9 != 1 && rem % 9 != 8) = false := by
    rcases hm9 with h | h | h <;> simp [h]
  rw [hcond2] at hok
  simp only [Bool.false_eq_true, ↓reduceIte] at hok
  have hlt := of_decide_eq_true hok
  set c := cbrtSearch rem 0 127 7
  have hxc : c ^ 3 < x ^ 3 := by
    have : c ^ 3 = c * c * c := by ring
    omega
  have hxc1 : x ^ 3 < (c + 1) ^ 3 := by
    have : (c + 1) ^ 3 = (c + 1) * (c + 1) * (c + 1) := by ring
    omega
  have h1 : c < x := by
    by_contra hle
    have : x ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  have h2 : x < c + 1 := by
    by_contra hle
    have : (c + 1) ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  omega

private def checkY (remWZ : ℕ) : ℕ → Bool
  | 0 => true
  | y + 1 =>
    let y3 := (y + 1) * (y + 1) * (y + 1)
    if y3 * 2 < remWZ then true
    else
      (if y3 ≤ remWZ then notCubeLt (remWZ - y3) y3 else true) && checkY remWZ y

private lemma checkY_sound (remWZ : ℕ) : ∀ hi : ℕ, checkY remWZ hi = true →
    ∀ x y : ℕ, 0 < x → x < y → y ≤ hi → x ^ 3 + y ^ 3 ≠ remWZ := by
  intro hi
  induction hi with
  | zero =>
    intro _ x y hx hxy hy
    omega
  | succ hi ih =>
    intro hok x y hx hxy hy
    unfold checkY at hok
    dsimp only at hok
    by_cases hlow : (hi + 1) * (hi + 1) * (hi + 1) * 2 < remWZ
    · intro heq
      have hxy3 : x ^ 3 < y ^ 3 := Nat.pow_lt_pow_left hxy (by decide)
      have hyhi : y ^ 3 ≤ (hi + 1) ^ 3 := Nat.pow_le_pow_left hy 3
      have hhi3 : (hi + 1) ^ 3 = (hi + 1) * (hi + 1) * (hi + 1) := by ring
      omega
    · rw [if_neg hlow, Bool.and_eq_true] at hok
      rcases eq_or_lt_of_le hy with rfl | hlt
      · intro heq
        have hy3 : (hi + 1) ^ 3 = (hi + 1) * (hi + 1) * (hi + 1) := by ring
        have hle : (hi + 1) * (hi + 1) * (hi + 1) ≤ remWZ := by omega
        have hok1 := hok.1
        rw [if_pos hle] at hok1
        exact notCubeLt_sound hx hxy hok1 (by omega)
      · exact ih hok.2 x y hx hxy (by omega)

private def checkZ (remW : ℕ) : ℕ → Bool
  | 0 => true
  | z + 1 =>
    let z3 := (z + 1) * (z + 1) * (z + 1)
    if z3 * 3 < remW then true
    else
      (if z3 ≤ remW then checkY (remW - z3) z else true) && checkZ remW z

private lemma checkZ_sound (remW : ℕ) : ∀ hi : ℕ, checkZ remW hi = true →
    ∀ x y z : ℕ, 0 < x → x < y → y < z → z ≤ hi → x ^ 3 + y ^ 3 + z ^ 3 ≠ remW := by
  intro hi
  induction hi with
  | zero =>
    intro _ x y z hx hxy hyz hz
    omega
  | succ hi ih =>
    intro hok x y z hx hxy hyz hz
    unfold checkZ at hok
    dsimp only at hok
    by_cases hlow : (hi + 1) * (hi + 1) * (hi + 1) * 3 < remW
    · intro heq
      have hxz : x ^ 3 < z ^ 3 := Nat.pow_lt_pow_left (by omega) (by decide)
      have hyz3 : y ^ 3 < z ^ 3 := Nat.pow_lt_pow_left hyz (by decide)
      have hzhi : z ^ 3 ≤ (hi + 1) ^ 3 := Nat.pow_le_pow_left hz 3
      have hhi3 : (hi + 1) ^ 3 = (hi + 1) * (hi + 1) * (hi + 1) := by ring
      omega
    · rw [if_neg hlow, Bool.and_eq_true] at hok
      rcases eq_or_lt_of_le hz with rfl | hlt
      · intro heq
        have hz3 : (hi + 1) ^ 3 = (hi + 1) * (hi + 1) * (hi + 1) := by ring
        have hle : (hi + 1) * (hi + 1) * (hi + 1) ≤ remW := by omega
        have hok1 := hok.1
        rw [if_pos hle] at hok1
        exact checkY_sound (remW - (hi + 1) * (hi + 1) * (hi + 1)) hi hok1 x y hx hxy
          (by omega) (by omega)
      · exact ih hok.2 x y z hx hxy hyz (by omega)

private def checkW : ℕ → Bool
  | 0 => true
  | w + 1 =>
    let w3 := (w + 1) * (w + 1) * (w + 1)
    if w3 * 4 < target then true
    else
      (if w3 ≤ target then checkZ (target - w3) w else true) && checkW w

private lemma checkW_sound : ∀ hi : ℕ, checkW hi = true →
    ∀ x y z w : ℕ, 0 < x → x < y → y < z → z < w → w ≤ hi →
      x ^ 3 + y ^ 3 + z ^ 3 + w ^ 3 ≠ target := by
  intro hi
  induction hi with
  | zero =>
    intro _ x y z w hx hxy hyz hzw hw
    omega
  | succ hi ih =>
    intro hok x y z w hx hxy hyz hzw hw
    unfold checkW at hok
    dsimp only at hok
    by_cases hlow : (hi + 1) * (hi + 1) * (hi + 1) * 4 < target
    · intro heq
      have hxw : x ^ 3 < w ^ 3 := Nat.pow_lt_pow_left (by omega) (by decide)
      have hyw : y ^ 3 < w ^ 3 := Nat.pow_lt_pow_left (by omega) (by decide)
      have hzw3 : z ^ 3 < w ^ 3 := Nat.pow_lt_pow_left hzw (by decide)
      have hwhi : w ^ 3 ≤ (hi + 1) ^ 3 := Nat.pow_le_pow_left hw 3
      have hhi3 : (hi + 1) ^ 3 = (hi + 1) * (hi + 1) * (hi + 1) := by ring
      omega
    · rw [if_neg hlow, Bool.and_eq_true] at hok
      rcases eq_or_lt_of_le hw with rfl | hlt
      · intro heq
        have hw3 : (hi + 1) ^ 3 = (hi + 1) * (hi + 1) * (hi + 1) := by ring
        have hle : (hi + 1) * (hi + 1) * (hi + 1) ≤ target := by omega
        have hok1 := hok.1
        rw [if_pos hle] at hok1
        exact checkZ_sound (target - (hi + 1) * (hi + 1) * (hi + 1)) hi hok1 x y z hx hxy hyz
          (by omega) (by omega)
      · exact ih hok.2 x y z w hx hxy hyz hzw (by omega)

private lemma checkW_120 : checkW 120 = true := by decide +kernel

end OeisA384132R1H1Proof

theorem OMA.solution : OMA.R_oeis_a384132_R1.H1 := by
  rintro ⟨x, y, z, w, hx, hxy, hyz, hzw, heq⟩
  have hw_le : w ≤ 120 := by
    by_contra hgt
    have hw3 : 121 ^ 3 ≤ w ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hx3 : 0 < x ^ 3 := pow_pos hx 3
    omega
  exact OeisA384132R1H1Proof.checkW_sound 120 OeisA384132R1H1Proof.checkW_120
    x y z w hx hxy hyz hzw hw_le heq
