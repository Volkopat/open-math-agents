import OMAStatements.S_oeis_a273676
namespace Adapt273676



def applyRule (r : ℕ) (c n s w e : Bool) : Bool :=
  r.testBit (c.toNat + 2 * (n.toNat + s.toNat + w.toNat + e.toNat))


def getCell (t : ℕ) (c : Bool × List (List Bool)) (x y : ℤ) : Bool :=
  if -↑t ≤ x ∧ x ≤ ↑t ∧ -↑t ≤ y ∧ y ≤ ↑t then
    (c.2.getD (y + ↑t).toNat []).getD (x + ↑t).toNat c.1
  else c.1


def stepCfg (r t : ℕ) (c : Bool × List (List Bool)) : Bool × List (List Bool) :=
  let g := getCell t c
  (applyRule r c.1 c.1 c.1 c.1 c.1,
   (List.range (2 * (t + 1) + 1)).map fun iy =>
     (List.range (2 * (t + 1) + 1)).map fun ix =>
       let x : ℤ := (ix : ℤ) - ↑(t + 1)
       let y : ℤ := (iy : ℤ) - ↑(t + 1)
       applyRule r (g x y) (g x (y - 1)) (g x (y + 1)) (g (x - 1) y) (g (x + 1) y))


def stageCfg (r : ℕ) : ℕ → Bool × List (List Bool)
  | 0 => (false, [[true]])
  | t + 1 => stepCfg r t (stageCfg r t)


def countOn (r t : ℕ) : ℕ :=
  ((stageCfg r t).2.map fun row => row.count true).sum


def a (n : ℕ) : ℕ := countOn 833 (2 ^ n - 1)


def a270222 (n : ℕ) : ℕ := countOn 131 (2 ^ n - 1)




open Adapt273676

namespace Scale833

def transitions : Array (Array (Array ℕ)) := #[
  #[#[0, 1, 1, 1, 2, 3, 3, 4], #[1, 1, 1, 1, 4, 4, 4, 4], #[5, 6, 6, 3, 5, 7, 7, 6], #[3, 4, 4, 4, 6, 3, 3, 4], #[4, 4, 4, 4, 4, 4, 4, 4], #[7, 5, 5, 7, 5, 7, 7, 5], #[7, 6, 6, 3, 5, 7, 7, 6], #[7, 5, 5, 7, 5, 7, 7, 5]]]

def outputs : Array Bool := #[true, false, false, false, true, true, true, false]

def lit (q : ℕ) := outputs[q]?.getD false

def code (t x y : Bool) := 4 * t.toNat + 2 * x.toNat + y.toNat

def go (q : ℕ) (t x y : Bool) : ℕ :=
  (((transitions[q / 16]?.getD #[])[q % 16]?.getD #[])[code t x y]?).getD 0

def digit (n : ℕ) (b : Bool) : ℕ := 2 * n + b.toNat

def prev (n : ℕ) : ℕ := if n = 0 then 1 else n - 1

lemma digit_half (n : ℕ) (b : Bool) : digit n b / 2 = n := by
  cases b <;> simp [digit] <;> omega

lemma digit_parity (n : ℕ) (b : Bool) : (digit n b % 2 == 1) = b := by
  cases b <;> simp [digit] <;> omega

lemma digit_zero (n : ℕ) (b : Bool) : (digit n b == 0) = ((n == 0) && !b) := by
  cases b <;> simp [digit]

lemma digit_next (n : ℕ) (b : Bool) :
    digit n b + 1 = digit (if b then n + 1 else n) (!b) := by
  cases b <;> simp [digit] <;> omega

lemma digit_prev (n : ℕ) (b : Bool) :
    prev (digit n b) = digit (if b || (n == 0) then n else prev n) (!b) := by
  cases n <;> cases b <;> simp [digit, prev] <;> omega

def address : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | w + 1, t, x, y => go (address w (t / 2) (x / 2) (y / 2)) (t % 2 == 1) (x % 2 == 1) (y % 2 == 1)

lemma address_digit (w t x y : ℕ) (bt bx by' : Bool) :
    address (w + 1) (digit t bt) (digit x bx) (digit y by') =
      go (address w t x y) bt bx by' := by
  simp only [address, digit_half, digit_parity]

structure Local where
  c : ℕ
  next : ℕ
  left : ℕ
  right : ℕ
  down : ℕ
  up : ℕ
  zx : Bool
  zy : Bool
  zt : Bool
  deriving DecidableEq, Inhabited

def position (w t x y : ℕ) : Local :=
  ⟨address (w + 1) t x y, address (w + 1) (t + 1) x y,
   address (w + 1) t (prev x) y, address (w + 1) t (x + 1) y,
   address (w + 1) t x (prev y), address (w + 1) t x (y + 1), x == 0, y == 0, t == 0⟩

def descend (g : Local) (t x y : Bool) : Local :=
  ⟨go g.c t x y, go (if t then g.next else g.c) (!t) x y,
   go (if x || g.zx then g.c else g.left) t (!x) y,
   go (if x then g.right else g.c) t (!x) y,
   go (if y || g.zy then g.c else g.down) t x (!y),
   go (if y then g.up else g.c) t x (!y),
   g.zx && !x, g.zy && !y, g.zt && !t⟩

lemma position_digit (w t x y : ℕ) (bt bx by' : Bool) :
    position (w + 1) (digit t bt) (digit x bx) (digit y by') =
      descend (position w t x y) bt bx by' := by
  simp only [position, descend, digit_next, digit_prev, digit_zero, address_digit]
  cases bt <;> cases bx <;> cases by' <;> by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    simp [hx, hy]

def localRule (r : ℕ) (c l h d u : Bool) : Bool :=
  r.testBit (c.toNat + 2 * (l.toNat + h.toNat + d.toNat + u.toNat))

def valid (s : Local) : Prop :=
  (s.zt = true → lit s.c = (s.zx && s.zy)) ∧
  lit s.next = localRule 833 (lit s.c) (lit s.left) (lit s.right) (lit s.down) (lit s.up) ∧
  lit s.next = localRule 849 (lit s.c) (lit s.left) (lit s.right) (lit s.down) (lit s.up)

instance (s : Local) : Decidable (valid s) := by unfold valid; infer_instance

def windows : Array (Array Local) := #[
  #[⟨0, 2, 1, 1, 1, 1, true, true, true⟩, ⟨1, 3, 1, 1, 0, 1, true, false, true⟩, ⟨1, 3, 0, 1, 1, 1, false, true, true⟩, ⟨1, 4, 1, 1, 1, 1, false, false, true⟩, ⟨2, 5, 3, 3, 3, 3, true, true, false⟩, ⟨3, 6, 4, 4, 2, 4, true, false, false⟩, ⟨3, 6, 2, 4, 4, 4, false, true, false⟩, ⟨4, 3, 3, 4, 3, 4, false, false, false⟩, ⟨1, 4, 1, 1, 1, 1, true, false, true⟩, ⟨4, 3, 4, 4, 3, 4, true, false, false⟩, ⟨4, 4, 4, 4, 4, 4, true, false, false⟩, ⟨4, 4, 4, 4, 4, 4, false, false, false⟩, ⟨1, 4, 1, 1, 1, 1, false, true, true⟩, ⟨4, 3, 3, 4, 4, 4, false, true, false⟩, ⟨4, 4, 4, 4, 4, 4, false, true, false⟩, ⟨5, 5, 6, 6, 6, 6, true, true, false⟩],
  #[⟨6, 7, 3, 3, 5, 3, true, false, false⟩, ⟨6, 7, 5, 3, 3, 3, false, true, false⟩, ⟨3, 6, 6, 4, 6, 4, false, false, false⟩, ⟨5, 7, 7, 7, 7, 7, true, true, false⟩, ⟨7, 5, 6, 6, 5, 6, true, false, false⟩, ⟨7, 5, 5, 6, 6, 6, false, true, false⟩, ⟨6, 7, 7, 3, 7, 3, false, false, false⟩, ⟨3, 6, 4, 4, 6, 4, true, false, false⟩, ⟨6, 7, 3, 3, 7, 3, true, false, false⟩, ⟨3, 6, 6, 4, 4, 4, false, true, false⟩, ⟨6, 7, 7, 3, 3, 3, false, true, false⟩, ⟨7, 5, 5, 5, 5, 5, true, true, false⟩, ⟨5, 7, 7, 7, 7, 7, true, false, false⟩, ⟨5, 7, 7, 7, 7, 7, false, true, false⟩, ⟨7, 5, 5, 6, 5, 6, false, false, false⟩, ⟨7, 5, 5, 5, 5, 5, true, false, false⟩],
  #[⟨7, 5, 5, 5, 5, 5, false, true, false⟩, ⟨5, 7, 7, 7, 7, 7, false, false, false⟩, ⟨7, 5, 5, 5, 5, 5, false, false, false⟩]]

def links : Array (Array (Array ℕ)) := #[
  #[#[0, 1, 2, 3, 4, 5, 6, 7], #[8, 8, 3, 3, 9, 10, 11, 11], #[12, 3, 12, 3, 13, 11, 14, 11], #[3, 3, 3, 3, 11, 11, 11, 11], #[15, 16, 17, 18, 19, 20, 21, 22], #[23, 9, 7, 11, 24, 23, 18, 7], #[25, 7, 13, 11, 26, 18, 25, 7], #[11, 11, 11, 11, 7, 11, 11, 11], #[8, 8, 3, 3, 10, 10, 11, 11], #[10, 10, 11, 11, 9, 10, 11, 11], #[10, 10, 11, 11, 10, 10, 11, 11], #[11, 11, 11, 11, 11, 11, 11, 11], #[12, 3, 12, 3, 14, 11, 14, 11], #[14, 11, 14, 11, 13, 11, 14, 11], #[14, 11, 14, 11, 14, 11, 14, 11], #[27, 28, 29, 30, 19, 31, 32, 33]],
  #[#[20, 24, 22, 18, 28, 20, 30, 22], #[21, 22, 26, 18, 29, 30, 21, 22], #[18, 7, 7, 11, 22, 18, 18, 7], #[27, 28, 29, 34, 19, 31, 32, 33], #[31, 28, 33, 30, 28, 31, 34, 33], #[32, 33, 29, 30, 29, 34, 32, 33], #[30, 22, 22, 18, 33, 30, 30, 22], #[23, 9, 7, 11, 24, 23, 18, 7], #[20, 24, 22, 18, 28, 20, 30, 22], #[25, 7, 13, 11, 26, 18, 25, 7], #[21, 22, 26, 18, 29, 30, 21, 22], #[27, 28, 29, 34, 19, 31, 32, 33], #[31, 28, 33, 34, 28, 31, 34, 33], #[32, 33, 29, 34, 29, 34, 32, 33], #[34, 33, 33, 30, 33, 34, 34, 33], #[31, 28, 33, 34, 28, 31, 34, 33]],
  #[#[32, 33, 29, 34, 29, 34, 32, 33], #[34, 33, 33, 34, 33, 34, 34, 33], #[34, 33, 33, 34, 33, 34, 34, 33]]]

abbrev Index := Fin 35

def window (i : Index) : Local := ((windows[i.val / 16]?.getD #[])[i.val % 16]?).getD default

def link (i : Index) (t x y : Bool) : Index :=
  ⟨((((links[i.val / 16]?.getD #[])[i.val % 16]?.getD #[])[code t x y]?).getD 0) % 35,
    Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma certificate : ∀ i : Index, valid (window i) ∧
    ∀ t x y : Bool, window (link i t x y) = descend (window i) t x y := by
  decide +kernel

lemma at_origin : position 0 0 0 0 = window 0 := by decide

lemma decomposes (n : ℕ) : digit (n / 2) (n % 2 == 1) = n := by
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h <;> simp [digit, h] <;> omega

lemma covered (w t x y : ℕ) (ht : t < 2 ^ w) (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    ∃ i, position w t x y = window i := by
  induction w generalizing t x y with
  | zero =>
    simp only [pow_zero] at ht hx hy
    obtain rfl : t = 0 := by omega
    obtain rfl : x = 0 := by omega
    obtain rfl : y = 0 := by omega
    exact ⟨0, at_origin⟩
  | succ w ih =>
    simp only [pow_succ] at ht hx hy
    obtain ⟨i, hi⟩ := ih (t / 2) (x / 2) (y / 2) (by omega) (by omega) (by omega)
    refine ⟨link i (t % 2 == 1) (x % 2 == 1) (y % 2 == 1), ?_⟩
    have h := position_digit w (t / 2) (x / 2) (y / 2) (t % 2 == 1) (x % 2 == 1) (y % 2 == 1)
    rw [decomposes, decomposes, decomposes, hi, ← (certificate i).2] at h
    exact h

lemma address_stable (w t x y : ℕ) (ht : t < 2 ^ w) (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    address (w + 1) t x y = address w t x y := by
  induction w generalizing t x y with
  | zero =>
    simp only [pow_zero] at ht hx hy
    have : t = 0 := by omega
    have : x = 0 := by omega
    have : y = 0 := by omega
    subst_vars
    decide
  | succ w ih =>
    simp only [pow_succ] at ht hx hy
    change go (address (w + 1) (t / 2) (x / 2) (y / 2)) _ _ _ = go (address w _ _ _) _ _ _
    rw [ih (t / 2) (x / 2) (y / 2) (by omega) (by omega) (by omega)]

lemma address_wider (w u t x y : ℕ) (hu : w ≤ u) (ht : t < 2 ^ w) (hx : x < 2 ^ w)
    (hy : y < 2 ^ w) : address u t x y = address w t x y := by
  induction u, hu using Nat.le_induction with
  | base => rfl
  | succ u hu ih =>
    have hpow : 2 ^ w ≤ (2 : ℕ) ^ u := Nat.pow_le_pow_right (by decide) hu
    rw [address_stable u t x y (by omega) (by omega) (by omega), ih]

def value (t x y : ℕ) := lit (address (t + x + y + 1) t x y)

lemma at_width (w t x y : ℕ) (ht : t < 2 ^ w) (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    value t x y = lit (address w t x y) := by
  unfold value
  by_cases h : w ≤ t + x + y + 1
  · rw [address_wider w _ _ _ _ h ht hx hy]
  · have hb := Nat.lt_two_pow_self (n := t + x + y + 1)
    rw [address_wider (t + x + y + 1) w _ _ _ (by omega) (by omega) (by omega) (by omega)]

lemma natural_law (r t x y : ℕ) (hr : r = 833 ∨ r = 849) :
    (t = 0 → value t x y = decide (x = 0 ∧ y = 0)) ∧
    value (t + 1) x y = localRule r (value t x y) (value t (prev x) y) (value t (x + 1) y)
      (value t x (prev y)) (value t x (y + 1)) := by
  let w := t + x + y + 2
  have hw : t + x + y + 2 < 2 ^ w := Nat.lt_two_pow_self
  obtain ⟨i, hi⟩ := covered w t x y (by omega) (by omega) (by omega)
  have h := (certificate i).1
  rw [← hi] at h
  simp only [valid, position] at h
  have hpow : t + x + y + 2 < 2 ^ (w + 1) := by rw [pow_succ]; omega
  have hpx : prev x ≤ x + 1 := by unfold prev; split <;> omega
  have hpy : prev y ≤ y + 1 := by unfold prev; split <;> omega
  rw [at_width (w + 1) t x y (by omega) (by omega) (by omega),
    at_width (w + 1) (t + 1) x y (by omega) (by omega) (by omega),
    at_width (w + 1) t (prev x) y (by omega) (by omega) (by omega),
    at_width (w + 1) t (x + 1) y (by omega) (by omega) (by omega),
    at_width (w + 1) t x (prev y) (by omega) (by omega) (by omega),
    at_width (w + 1) t x (y + 1) (by omega) (by omega) (by omega)]
  constructor
  · intro ht
    have h0 := h.1 (by simp [ht])
    cases x <;> cases y <;> simpa using h0
  · rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2

def plane (t : ℕ) (x y : ℤ) := value t x.natAbs y.natAbs

lemma plane_zero (x y : ℤ) : plane 0 x y = decide (x = 0 ∧ y = 0) := by
  simpa [plane] using (natural_law 833 0 x.natAbs y.natAbs (Or.inl rfl : 833 = 833 ∨ 833 = 849)).1 rfl

lemma neighbors (x : ℤ) :
    ((x - 1).natAbs = prev x.natAbs ∧ (x + 1).natAbs = x.natAbs + 1) ∨
    ((x + 1).natAbs = prev x.natAbs ∧ (x - 1).natAbs = x.natAbs + 1) := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · right
    have a := Int.ofNat_natAbs_of_nonpos (show x ≤ 0 by omega)
    have b := Int.ofNat_natAbs_of_nonpos (show x + 1 ≤ 0 by omega)
    have c := Int.ofNat_natAbs_of_nonpos (show x - 1 ≤ 0 by omega)
    unfold prev; split <;> omega
  · decide
  · left
    have a := Int.natAbs_of_nonneg (show 0 ≤ x by omega)
    have b := Int.natAbs_of_nonneg (show 0 ≤ x + 1 by omega)
    have c := Int.natAbs_of_nonneg (show 0 ≤ x - 1 by omega)
    unfold prev; split <;> omega

lemma plane_step (r t : ℕ) (x y : ℤ) (hr : r = 833 ∨ r = 849) :
    plane (t + 1) x y = localRule r (plane t x y) (plane t (x - 1) y) (plane t (x + 1) y)
      (plane t x (y - 1)) (plane t x (y + 1)) := by
  unfold plane
  rw [(natural_law r t x.natAbs y.natAbs hr).2]
  unfold localRule
  rcases neighbors x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases neighbors y with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rw [h1, h2, h3, h4] <;> ac_rfl

def gridRows (t : ℕ) (f : ℤ → ℤ → Bool) : List (List Bool) :=
  (List.range (2 * t + 1)).map fun (j : ℕ) =>
    (List.range (2 * t + 1)).map fun (i : ℕ) => f ((i : ℤ) - ↑t) ((j : ℤ) - ↑t)

def background (r : ℕ) : ℕ → Bool
  | 0 => false
  | t + 1 => applyRule r (background r t) (background r t) (background r t)
      (background r t) (background r t)

lemma applyRule_eq_localRule (r : ℕ) (c n s w e : Bool) :
    applyRule r c n s w e = localRule r c w e n s := by
  unfold applyRule localRule; congr 1; omega

lemma outside (r t : ℕ) (hr : r = 833 ∨ r = 849) (x y : ℤ)
    (h : x < -(t : ℤ) ∨ (t : ℤ) < x ∨ y < -(t : ℤ) ∨ (t : ℤ) < y) :
    plane t x y = background r t := by
  induction t generalizing x y with
  | zero => rw [plane_zero]; simp [background]; omega
  | succ t ih =>
    simp only [Nat.cast_succ] at h
    rw [plane_step r t x y hr, ih x y (by omega), ih (x - 1) y (by omega),
      ih (x + 1) y (by omega), ih x (y - 1) (by omega), ih x (y + 1) (by omega)]
    rw [background]
    exact (applyRule_eq_localRule r _ _ _ _ _).symm

lemma getD_map_range {α : Type} (n : ℕ) (f : ℕ → α) (i : ℕ) (d : α) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD, hi]

lemma getCell_gridRows (t : ℕ) (bg : Bool) (f : ℤ → ℤ → Bool)
    (hout : ∀ u v : ℤ, u < -(t : ℤ) ∨ (t : ℤ) < u ∨ v < -(t : ℤ) ∨ (t : ℤ) < v → f u v = bg)
    (x y : ℤ) :
    getCell t (bg, gridRows t f) x y = f x y := by
  unfold getCell
  split_ifs with h
  · rcases h with ⟨hx1, hx2, hy1, hy2⟩
    have hiy : (y + ↑t).toNat < 2 * t + 1 := by omega
    have hix : (x + ↑t).toNat < 2 * t + 1 := by omega
    have hiy_eq : (((y + ↑t).toNat : ℤ) - ↑t) = y := by omega
    have hix_eq : (((x + ↑t).toNat : ℤ) - ↑t) = x := by omega
    unfold gridRows
    rw [getD_map_range _ _ _ _ hiy, getD_map_range _ _ _ _ hix, hix_eq, hiy_eq]
  · symm; apply hout; omega

lemma flatMap_pure_map {α β γ : Type} (xs : List α) (c : α → β) (f : β → γ) :
    List.map f (List.flatMap (fun a => [c a]) xs) = List.map (fun a => f (c a)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma stages (r t : ℕ) (hr : r = 833 ∨ r = 849) :
    stageCfg r t = (background r t, gridRows t (plane t)) := by
  induction t with
  | zero =>
    simp [stageCfg, background, gridRows, plane_zero]
  | succ t ih =>
    rw [stageCfg, ih]
    have hg : getCell t (background r t, gridRows t (plane t)) = plane t := by
      funext x y; exact getCell_gridRows t (background r t) (plane t) (outside r t hr) x y
    dsimp only [stepCfg]
    rw [hg]
    refine Prod.ext rfl ?_
    simp only [List.bind_eq_flatMap, List.pure_def, flatMap_pure_map, gridRows]
    apply List.map_congr_left; intro iy _
    apply List.map_congr_left; intro ix _
    rw [plane_step r t _ _ hr]
    exact applyRule_eq_localRule r _ _ _ _ _

lemma count_map_range (n : ℕ) (g : ℕ → Bool) :
    (((List.range n).map g).count true : ℤ) = ∑ i ∈ Finset.range n, ((g i).toNat : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.count_append, Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil]
    push_cast
    rw [ih]
    cases g n <;> simp

lemma sum_map_range (n : ℕ) (g : ℕ → ℕ) :
    (Nat.cast (((List.range n).map g).sum) : ℤ) = ∑ i ∈ Finset.range n, (g i : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, Nat.cast_add, ih]
    simp

lemma sum_gridRows (t : ℕ) (f : ℤ → ℤ → Bool) :
    (Nat.cast (((gridRows t f).map fun row => row.count true).sum) : ℤ) =
      ∑ j ∈ Finset.range (2 * t + 1), ∑ i ∈ Finset.range (2 * t + 1),
        ((f ((i : ℤ) - ↑t) ((j : ℤ) - ↑t)).toNat : ℤ) := by
  unfold gridRows
  simp only [List.map_map, Function.comp_def]
  rw [sum_map_range]
  apply Finset.sum_congr rfl
  intro j _
  exact count_map_range (2 * t + 1) (fun i => f ((i : ℤ) - ↑t) ((j : ℤ) - ↑t))

lemma reflect_sum (t : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range (2 * t + 1), f (((i : ℤ) - ↑t).natAbs) =
      2 * (∑ i ∈ Finset.range (t + 1), f i) - f 0 := by
  rw [show 2 * t + 1 = (t + 1) + t by omega, Finset.sum_range_add]
  have h₁ : ∑ i ∈ Finset.range (t + 1), f (((i : ℤ) - ↑t).natAbs) =
      ∑ i ∈ Finset.range (t + 1), f i := by
    rw [← Finset.sum_range_reflect f (t + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    congr 1
    have := Int.ofNat_natAbs_of_nonpos (show (i : ℤ) - ↑t ≤ 0 by omega)
    omega
  rw [h₁]
  have h₂ : ∑ i ∈ Finset.range t, f ((((t + 1 + i : ℕ) : ℤ) - ↑t).natAbs) =
      ∑ i ∈ Finset.range t, f (i + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast
    rw [show (t : ℤ) + 1 + i - ↑t = ↑(i + 1 : ℕ) by omega]
    rfl
  rw [h₂]
  have := Finset.sum_range_succ' f t
  omega

def span (b : Bool) (n : ℕ) := if b then 2 ^ n else 1

def pick (b : Bool) (f : Bool → ℤ) := if b then f false + f true else f false

def mix (u v : Bool) (f : ℕ → ℤ) (q : ℕ) :=
  pick v fun y => pick u fun x => f (go q true x y)

def total (n : ℕ) (u v : Bool) (f : ℕ → ℤ) : ℤ :=
  ∑ j ∈ Finset.range (span v n), ∑ i ∈ Finset.range (span u n),
    f (address n (2 ^ n - 1) i j)

def weight (q : ℕ) : ℤ := (lit q).toNat

def count (n : ℕ) (u v : Bool) := total n u v weight

lemma paired (k : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range (2 * k), f i =
      ∑ i ∈ Finset.range k, (f (2 * i) + f (2 * i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    omega

lemma span_split (b : Bool) (n : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range (span b (n + 1)), f i =
      ∑ i ∈ Finset.range (span b n), pick b (fun bit => f (digit i bit)) := by
  cases b
  · simp [span, pick, digit]
  · simp only [span, ↓reduceIte, pick, digit, Bool.toNat_false,
      Bool.toNat_true, Nat.add_zero, pow_succ]
    rw [Nat.mul_comm, paired]

lemma total_step (n : ℕ) (u v : Bool) (f : ℕ → ℤ) :
    total (n + 1) u v f = total n u v (mix u v f) := by
  have ht : 2 ^ (n + 1) - 1 = digit (2 ^ n - 1) true := by
    have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    simp [digit, pow_succ]; omega
  unfold total
  rw [span_split v n]
  apply Finset.sum_congr rfl
  intro j _
  cases v <;> simp only [mix, pick, Bool.false_eq_true, ↓reduceIte, Finset.sum_add_distrib,
    span_split u n, ht, address_digit]
  all_goals first | rfl | rw [Finset.sum_add_distrib]

lemma small_go : ∀ q : Fin 8, ∀ t x y : Bool, go q.val t x y < 8 := by decide +kernel

lemma small_address (w t x y : ℕ) : address w t x y < 8 := by
  induction w generalizing t x y with
  | zero => change 0 < 8; decide
  | succ w ih => exact small_go ⟨_, ih (t / 2) (x / 2) (y / 2)⟩ _ _ _

def iterate (k : ℕ) (u v : Bool) : ℕ → ℤ :=
  match k with
  | 0 => weight
  | k + 1 => mix u v (iterate k u v)

def iterVec (k : ℕ) (u v : Bool) : List ℤ :=
  match k with
  | 0 => (List.range 8).map weight
  | k + 1 =>
    let prev := iterVec k u v
    (List.range 8).map (fun q => mix u v (fun s => prev.getD s 0) q)

lemma iterVec_eq (k : ℕ) (u v : Bool) :
    ∀ q < 8, (iterVec k u v).getD q 0 = iterate k u v q := by
  induction k with
  | zero =>
    intro q hq
    exact getD_map_range 8 weight q 0 hq
  | succ k ih =>
    intro q hq
    unfold iterVec iterate
    dsimp only
    rw [getD_map_range 8 _ q 0 hq]
    unfold mix
    congr 1; funext y; congr 1; funext x
    exact ih (go q true x y) (small_go ⟨q, hq⟩ true x y)

lemma shift_total (n k : ℕ) (u v : Bool) :
    count (n + k) u v = total n u v (iterate k u v) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [show n + (k + 1) = (n + 1) + k by omega, ih, total_step]
    rfl

set_option maxHeartbeats 4000000 in
lemma iter_vec_rec : ∀ u v : Bool,
    let v2 := iterVec 2 u v
    let v3 := iterVec 3 u v
    let v4 := iterVec 4 u v
    let v5 := iterVec 5 u v
    ∀ q : Fin 8, v5.getD q.val 0 = 7 * v4.getD q.val 0 - 14 * v3.getD q.val 0 + 8 * v2.getD q.val 0 := by
  decide +kernel

lemma iter_rec (u v : Bool) (q : Fin 8) :
    iterate 5 u v q.val = 7 * iterate 4 u v q.val - 14 * iterate 3 u v q.val + 8 * iterate 2 u v q.val := by
  simpa only [iterVec_eq _ u v q.val q.isLt] using iter_vec_rec u v q

lemma count_rec (n : ℕ) (u v : Bool) :
    count (n + 5) u v = 7 * count (n + 4) u v - 14 * count (n + 3) u v + 8 * count (n + 2) u v := by
  simp only [shift_total, total, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro x _
  exact iter_rec u v ⟨_, small_address n _ x y⟩

lemma reflect_square (t : ℕ) (f : ℕ → ℕ → ℤ) :
    ∑ j ∈ Finset.range (2 * t + 1), ∑ i ∈ Finset.range (2 * t + 1),
      f (((i : ℤ) - ↑t).natAbs) (((j : ℤ) - ↑t).natAbs) =
    4 * (∑ j ∈ Finset.range (t + 1), ∑ i ∈ Finset.range (t + 1), f i j) -
      2 * (∑ j ∈ Finset.range (t + 1), f 0 j) - 2 * (∑ i ∈ Finset.range (t + 1), f i 0) + f 0 0 := by
  rw [reflect_sum t (fun y => ∑ i ∈ Finset.range (2 * t + 1), f (((i : ℤ) - ↑t).natAbs) y)]
  have inner (y : ℕ) := reflect_sum t (fun i => f i y)
  simp only [inner]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma count_eq (n : ℕ) (u v : Bool) :
    count n u v = ∑ j ∈ Finset.range (span v n), ∑ i ∈ Finset.range (span u n),
      ((value (2 ^ n - 1) i j).toNat : ℤ) := by
  have hpos : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  unfold count total weight
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro i hi
  simp only [Finset.mem_range] at hi hj
  have hb (b : Bool) : span b n ≤ 2 ^ n := by cases b <;> simp [span, Nat.one_le_two_pow]
  rw [at_width n _ _ _ (by omega) (lt_of_lt_of_le hi (hb u)) (lt_of_lt_of_le hj (hb v))]

lemma count_eq_iterVec (k : ℕ) (u v : Bool) :
    count k u v = (iterVec k u v).getD 0 0 := by
  have h := shift_total 0 k u v
  rw [Nat.zero_add] at h
  rw [h]
  have su : span u 0 = 1 := by cases u <;> rfl
  have sv : span v 0 = 1 := by cases v <;> rfl
  unfold total
  rw [su, sv]
  simp only [Finset.sum_range_one, address]
  exact (iterVec_eq k u v 0 (by decide)).symm

lemma sampled_eq (n r : ℕ) (hr : r = 833 ∨ r = 849) : (countOn r (2 ^ n - 1) : ℤ) =
    4 * count n true true - 2 * count n false true - 2 * count n true false + count n false false := by
  have h : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  unfold countOn
  rw [stages r _ hr]
  dsimp only
  rw [sum_gridRows]
  unfold plane
  rw [reflect_square (2 ^ n - 1) (fun i j => ((value (2 ^ n - 1) i j).toNat : ℤ))]
  simp only [count_eq, span, ↓reduceIte, Bool.false_eq_true, Finset.sum_range_one,
    show (2 : ℕ) ^ n - 1 + 1 = 2 ^ n by omega]

lemma sampled_fast (n r : ℕ) (hr : r = 833 ∨ r = 849) : (countOn r (2 ^ n - 1) : ℤ) =
    4 * (iterVec n true true).getD 0 0 - 2 * (iterVec n false true).getD 0 0 -
      2 * (iterVec n true false).getD 0 0 + (iterVec n false false).getD 0 0 := by
  rw [sampled_eq n r hr]
  simp only [count_eq_iterVec]

end Scale833


namespace Scale131

def transitions : Array (Array (Array ℕ)) := #[
  #[#[0, 1, 1, 1, 2, 3, 3, 4], #[1, 1, 1, 1, 4, 4, 4, 4], #[5, 6, 7, 1, 5, 8, 9, 10], #[0, 1, 1, 1, 2, 3, 3, 4], #[1, 1, 1, 1, 4, 4, 4, 4], #[5, 11, 11, 5, 5, 11, 11, 5], #[5, 6, 12, 1, 5, 8, 12, 13], #[5, 12, 7, 1, 5, 12, 9, 14], #[5, 11, 12, 15, 5, 11, 16, 17], #[5, 12, 11, 18, 5, 16, 11, 19], #[1, 20, 21, 1, 10, 22, 23, 10], #[5, 11, 11, 5, 5, 11, 11, 5], #[5, 12, 12, 1, 5, 12, 12, 4], #[1, 20, 1, 1, 13, 22, 4, 13], #[1, 1, 21, 1, 14, 4, 23, 14], #[24, 11, 1, 15, 25, 11, 26, 17]],
  #[#[5, 12, 12, 27, 5, 16, 16, 28], #[24, 11, 29, 30, 31, 11, 32, 33], #[34, 1, 11, 18, 35, 26, 11, 19], #[34, 36, 11, 30, 37, 38, 11, 33], #[1, 20, 1, 1, 13, 22, 4, 13], #[1, 1, 21, 1, 14, 4, 23, 14], #[39, 11, 1, 15, 40, 11, 41, 17], #[42, 1, 11, 18, 43, 41, 11, 19], #[24, 11, 1, 24, 25, 11, 4, 25], #[24, 11, 1, 24, 25, 11, 4, 25], #[1, 1, 1, 27, 4, 26, 26, 28], #[1, 1, 1, 27, 4, 26, 26, 28], #[1, 36, 29, 30, 10, 38, 32, 33], #[1, 44, 29, 30, 14, 45, 32, 33], #[30, 11, 11, 5, 33, 11, 11, 5], #[24, 11, 21, 24, 31, 11, 23, 31]],
  #[#[42, 44, 11, 30, 43, 46, 11, 33], #[30, 11, 11, 5, 33, 11, 11, 5], #[34, 1, 11, 34, 35, 4, 11, 35], #[34, 1, 11, 34, 35, 4, 11, 35], #[1, 36, 44, 30, 13, 38, 45, 33], #[34, 20, 11, 34, 37, 22, 11, 37], #[39, 11, 44, 30, 40, 11, 46, 33], #[39, 11, 1, 24, 40, 11, 3, 25], #[5, 11, 7, 24, 5, 11, 9, 31], #[0, 1, 1, 27, 2, 41, 41, 28], #[42, 1, 11, 34, 43, 3, 11, 35], #[5, 6, 11, 34, 5, 8, 11, 37], #[1, 44, 44, 30, 4, 45, 45, 33], #[1, 44, 44, 30, 4, 45, 45, 33], #[0, 44, 44, 30, 2, 46, 46, 33]]]

def outputs : Array Bool := #[true, false, true, false, true, true, false, false, false, false, true, false, false, true, true, false, false, true, false, true, false, false, false, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false]

def lit (q : ℕ) := outputs[q]?.getD false

def code (t x y : Bool) := 4 * t.toNat + 2 * x.toNat + y.toNat

def go (q : ℕ) (t x y : Bool) : ℕ :=
  (((transitions[q / 16]?.getD #[])[q % 16]?.getD #[])[code t x y]?).getD 0

def digit (n : ℕ) (b : Bool) : ℕ := 2 * n + b.toNat

def prev (n : ℕ) : ℕ := if n = 0 then 1 else n - 1

lemma digit_half (n : ℕ) (b : Bool) : digit n b / 2 = n := by
  cases b <;> simp [digit] <;> omega

lemma digit_parity (n : ℕ) (b : Bool) : (digit n b % 2 == 1) = b := by
  cases b <;> simp [digit] <;> omega

lemma digit_zero (n : ℕ) (b : Bool) : (digit n b == 0) = ((n == 0) && !b) := by
  cases b <;> simp [digit]

lemma digit_next (n : ℕ) (b : Bool) :
    digit n b + 1 = digit (if b then n + 1 else n) (!b) := by
  cases b <;> simp [digit] <;> omega

lemma digit_prev (n : ℕ) (b : Bool) :
    prev (digit n b) = digit (if b || (n == 0) then n else prev n) (!b) := by
  cases n <;> cases b <;> simp [digit, prev] <;> omega

def address : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | w + 1, t, x, y => go (address w (t / 2) (x / 2) (y / 2)) (t % 2 == 1) (x % 2 == 1) (y % 2 == 1)

lemma address_digit (w t x y : ℕ) (bt bx by' : Bool) :
    address (w + 1) (digit t bt) (digit x bx) (digit y by') =
      go (address w t x y) bt bx by' := by
  simp only [address, digit_half, digit_parity]

structure Local where
  c : ℕ
  next : ℕ
  left : ℕ
  right : ℕ
  down : ℕ
  up : ℕ
  zx : Bool
  zy : Bool
  zt : Bool
  deriving DecidableEq, Inhabited

def position (w t x y : ℕ) : Local :=
  ⟨address (w + 1) t x y, address (w + 1) (t + 1) x y,
   address (w + 1) t (prev x) y, address (w + 1) t (x + 1) y,
   address (w + 1) t x (prev y), address (w + 1) t x (y + 1), x == 0, y == 0, t == 0⟩

def descend (g : Local) (t x y : Bool) : Local :=
  ⟨go g.c t x y, go (if t then g.next else g.c) (!t) x y,
   go (if x || g.zx then g.c else g.left) t (!x) y,
   go (if x then g.right else g.c) t (!x) y,
   go (if y || g.zy then g.c else g.down) t x (!y),
   go (if y then g.up else g.c) t x (!y),
   g.zx && !x, g.zy && !y, g.zt && !t⟩

lemma position_digit (w t x y : ℕ) (bt bx by' : Bool) :
    position (w + 1) (digit t bt) (digit x bx) (digit y by') =
      descend (position w t x y) bt bx by' := by
  simp only [position, descend, digit_next, digit_prev, digit_zero, address_digit]
  cases bt <;> cases bx <;> cases by' <;> by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    simp [hx, hy]

def localRule (r : ℕ) (c l h d u : Bool) : Bool :=
  r.testBit (c.toNat + 2 * (l.toNat + h.toNat + d.toNat + u.toNat))

def valid (s : Local) : Prop :=
  (s.zt = true → lit s.c = (s.zx && s.zy)) ∧
  lit s.next = localRule 131 (lit s.c) (lit s.left) (lit s.right) (lit s.down) (lit s.up)

instance (s : Local) : Decidable (valid s) := by unfold valid; infer_instance

def windows : Array (Array Local) := #[
  #[⟨0, 2, 1, 1, 1, 1, true, true, true⟩, ⟨1, 3, 1, 1, 0, 1, true, false, true⟩, ⟨1, 3, 0, 1, 1, 1, false, true, true⟩, ⟨1, 4, 1, 1, 1, 1, false, false, true⟩, ⟨2, 5, 3, 3, 3, 3, true, true, false⟩, ⟨3, 6, 4, 4, 2, 4, true, false, false⟩, ⟨3, 7, 2, 4, 4, 4, false, true, false⟩, ⟨4, 1, 3, 4, 3, 4, false, false, false⟩, ⟨1, 4, 1, 1, 1, 1, true, false, true⟩, ⟨4, 0, 4, 4, 3, 4, true, false, false⟩, ⟨4, 1, 4, 4, 4, 4, true, false, false⟩, ⟨4, 1, 4, 4, 4, 4, false, false, false⟩, ⟨1, 4, 1, 1, 1, 1, false, true, true⟩, ⟨4, 0, 3, 4, 4, 4, false, true, false⟩, ⟨4, 1, 4, 4, 4, 4, false, true, false⟩, ⟨5, 5, 7, 7, 6, 6, true, true, false⟩],
  #[⟨6, 8, 1, 1, 5, 0, true, false, false⟩, ⟨7, 9, 5, 0, 1, 1, false, true, false⟩, ⟨1, 10, 6, 1, 7, 1, false, false, false⟩, ⟨5, 5, 9, 9, 8, 8, true, true, false⟩, ⟨8, 11, 10, 10, 5, 2, true, false, false⟩, ⟨9, 11, 5, 2, 10, 10, false, true, false⟩, ⟨10, 5, 8, 3, 9, 3, false, false, false⟩, ⟨0, 2, 1, 1, 6, 1, true, false, false⟩, ⟨1, 3, 1, 1, 0, 1, true, false, false⟩, ⟨1, 3, 0, 1, 1, 1, false, false, false⟩, ⟨1, 4, 1, 1, 1, 1, false, false, false⟩, ⟨2, 5, 3, 3, 8, 3, true, false, false⟩, ⟨3, 12, 2, 4, 10, 4, false, false, false⟩, ⟨0, 2, 7, 1, 1, 1, false, true, false⟩, ⟨1, 3, 1, 1, 0, 1, false, false, false⟩, ⟨1, 3, 0, 1, 1, 1, false, true, false⟩],
  #[⟨2, 5, 9, 3, 3, 3, false, true, false⟩, ⟨3, 12, 10, 4, 2, 4, false, false, false⟩, ⟨1, 4, 1, 1, 1, 1, true, false, false⟩, ⟨1, 4, 1, 1, 1, 1, false, true, false⟩, ⟨5, 5, 11, 11, 11, 11, true, true, false⟩, ⟨11, 11, 5, 5, 5, 5, true, false, false⟩, ⟨11, 11, 5, 5, 5, 5, false, true, false⟩, ⟨5, 5, 11, 12, 11, 12, false, false, false⟩, ⟨5, 5, 12, 12, 11, 6, true, false, false⟩, ⟨12, 12, 5, 1, 5, 1, false, false, false⟩, ⟨1, 13, 6, 1, 12, 1, false, false, false⟩, ⟨5, 5, 12, 12, 11, 8, true, false, false⟩, ⟨8, 11, 13, 13, 5, 2, true, false, false⟩, ⟨12, 12, 5, 4, 5, 13, false, false, false⟩, ⟨13, 15, 8, 4, 12, 3, false, false, false⟩, ⟨5, 5, 11, 7, 12, 12, false, true, false⟩],
  #[⟨1, 14, 12, 1, 7, 1, false, false, false⟩, ⟨5, 5, 11, 9, 12, 12, false, true, false⟩, ⟨12, 12, 5, 14, 5, 4, false, false, false⟩, ⟨9, 11, 5, 2, 14, 14, false, true, false⟩, ⟨14, 18, 12, 3, 9, 4, false, false, false⟩, ⟨1, 4, 12, 1, 12, 1, false, false, false⟩, ⟨4, 1, 12, 4, 12, 4, false, false, false⟩, ⟨4, 20, 13, 4, 4, 4, false, false, false⟩, ⟨4, 21, 4, 4, 14, 4, false, false, false⟩, ⟨5, 5, 11, 16, 11, 16, false, false, false⟩, ⟨5, 5, 12, 12, 11, 11, true, false, false⟩, ⟨11, 11, 15, 15, 5, 5, true, false, false⟩, ⟨12, 16, 5, 1, 5, 15, false, false, false⟩, ⟨15, 17, 11, 20, 12, 7, false, false, false⟩, ⟨5, 5, 16, 16, 11, 11, true, false, false⟩, ⟨11, 11, 17, 17, 5, 5, true, false, false⟩],
  #[⟨16, 11, 5, 10, 5, 17, false, false, false⟩, ⟨17, 5, 11, 22, 16, 9, false, false, false⟩, ⟨5, 5, 11, 11, 12, 12, false, true, false⟩, ⟨12, 16, 5, 18, 5, 1, false, false, false⟩, ⟨11, 11, 5, 5, 18, 18, false, true, false⟩, ⟨18, 19, 12, 6, 11, 21, false, false, false⟩, ⟨5, 5, 11, 11, 16, 16, false, true, false⟩, ⟨16, 11, 5, 19, 5, 10, false, false, false⟩, ⟨11, 11, 5, 5, 19, 19, false, true, false⟩, ⟨19, 5, 16, 8, 11, 23, false, false, false⟩, ⟨1, 10, 12, 21, 12, 20, false, false, false⟩, ⟨20, 22, 15, 1, 1, 0, false, false, false⟩, ⟨21, 23, 1, 0, 18, 1, false, false, false⟩, ⟨1, 10, 20, 1, 21, 1, false, false, false⟩, ⟨10, 5, 16, 23, 16, 22, false, false, false⟩, ⟨22, 11, 17, 10, 10, 2, false, false, false⟩],
  #[⟨23, 11, 10, 2, 19, 10, false, false, false⟩, ⟨10, 5, 22, 3, 23, 3, false, false, false⟩, ⟨3, 7, 2, 4, 13, 4, false, false, false⟩, ⟨4, 0, 3, 4, 4, 4, false, false, false⟩, ⟨5, 5, 7, 7, 11, 6, true, false, false⟩, ⟨7, 9, 5, 0, 15, 1, false, false, false⟩, ⟨5, 5, 9, 9, 11, 8, true, false, false⟩, ⟨9, 11, 5, 2, 17, 10, false, false, false⟩, ⟨0, 2, 7, 1, 20, 1, false, false, false⟩, ⟨2, 5, 9, 3, 22, 3, false, false, false⟩, ⟨3, 6, 14, 4, 2, 4, false, false, false⟩, ⟨4, 0, 4, 4, 3, 4, false, false, false⟩, ⟨5, 5, 11, 7, 6, 6, false, true, false⟩, ⟨6, 8, 18, 1, 5, 0, false, false, false⟩, ⟨5, 5, 11, 9, 8, 8, false, true, false⟩, ⟨8, 11, 19, 10, 5, 2, false, false, false⟩],
  #[⟨0, 2, 21, 1, 6, 1, false, false, false⟩, ⟨2, 5, 23, 3, 8, 3, false, false, false⟩, ⟨5, 5, 11, 11, 11, 11, false, false, false⟩, ⟨5, 5, 11, 11, 11, 11, true, false, false⟩, ⟨11, 11, 5, 5, 5, 5, false, false, false⟩, ⟨5, 5, 11, 11, 11, 11, false, true, false⟩, ⟨12, 12, 5, 4, 5, 4, false, false, false⟩, ⟨5, 5, 11, 12, 11, 16, false, false, false⟩, ⟨16, 11, 5, 13, 5, 17, false, false, false⟩, ⟨1, 13, 12, 1, 12, 20, false, false, false⟩, ⟨1, 13, 20, 1, 1, 1, false, false, false⟩, ⟨13, 24, 16, 4, 12, 22, false, false, false⟩, ⟨22, 11, 17, 13, 13, 2, false, false, false⟩, ⟨4, 1, 13, 4, 4, 13, false, false, false⟩, ⟨13, 15, 22, 4, 4, 3, false, false, false⟩, ⟨5, 5, 11, 16, 11, 12, false, false, false⟩],
  #[⟨16, 11, 5, 19, 5, 14, false, false, false⟩, ⟨1, 14, 12, 21, 12, 1, false, false, false⟩, ⟨1, 14, 1, 1, 21, 1, false, false, false⟩, ⟨14, 34, 12, 23, 16, 4, false, false, false⟩, ⟨4, 1, 4, 14, 14, 4, false, false, false⟩, ⟨23, 11, 14, 2, 19, 14, false, false, false⟩, ⟨14, 18, 4, 3, 23, 4, false, false, false⟩, ⟨5, 5, 11, 12, 11, 11, false, false, false⟩, ⟨11, 11, 5, 24, 5, 5, false, false, false⟩, ⟨11, 11, 5, 25, 5, 5, false, false, false⟩, ⟨12, 12, 5, 1, 5, 24, false, false, false⟩, ⟨12, 12, 5, 4, 5, 25, false, false, false⟩, ⟨4, 27, 12, 4, 12, 26, false, false, false⟩, ⟨24, 25, 11, 1, 12, 11, false, false, false⟩, ⟨11, 11, 5, 15, 24, 5, false, false, false⟩, ⟨1, 26, 24, 1, 1, 15, false, false, false⟩],
  #[⟨15, 17, 11, 20, 1, 7, false, false, false⟩, ⟨25, 24, 11, 26, 12, 11, false, false, false⟩, ⟨11, 11, 5, 17, 25, 5, false, false, false⟩, ⟨26, 29, 25, 13, 4, 17, false, false, false⟩, ⟨17, 30, 11, 22, 26, 9, false, false, false⟩, ⟨5, 5, 11, 16, 11, 11, false, false, false⟩, ⟨11, 11, 5, 31, 5, 5, false, false, false⟩, ⟨12, 16, 5, 27, 5, 24, false, false, false⟩, ⟨12, 16, 5, 1, 5, 27, false, false, false⟩, ⟨27, 28, 12, 20, 12, 29, false, false, false⟩, ⟨16, 11, 5, 28, 5, 31, false, false, false⟩, ⟨16, 11, 5, 10, 5, 28, false, false, false⟩, ⟨28, 5, 16, 22, 16, 32, false, false, false⟩, ⟨24, 31, 11, 29, 12, 11, false, false, false⟩, ⟨11, 11, 5, 30, 24, 5, false, false, false⟩, ⟨29, 32, 24, 39, 27, 30, false, false, false⟩],
  #[⟨30, 33, 11, 11, 29, 11, false, false, false⟩, ⟨31, 5, 11, 32, 16, 11, false, false, false⟩, ⟨11, 11, 5, 33, 31, 5, false, false, false⟩, ⟨32, 11, 31, 40, 28, 33, false, false, false⟩, ⟨33, 5, 11, 11, 32, 11, false, false, false⟩, ⟨5, 5, 11, 11, 11, 12, false, false, false⟩, ⟨12, 12, 5, 34, 5, 1, false, false, false⟩, ⟨12, 12, 5, 35, 5, 4, false, false, false⟩, ⟨4, 27, 12, 26, 12, 4, false, false, false⟩, ⟨11, 11, 5, 5, 5, 34, false, false, false⟩, ⟨11, 11, 5, 5, 5, 35, false, false, false⟩, ⟨34, 35, 12, 11, 11, 1, false, false, false⟩, ⟨1, 26, 1, 18, 34, 1, false, false, false⟩, ⟨11, 11, 34, 5, 5, 18, false, false, false⟩, ⟨18, 19, 1, 6, 11, 21, false, false, false⟩, ⟨35, 34, 12, 11, 11, 26, false, false, false⟩],
  #[⟨26, 36, 4, 19, 35, 14, false, false, false⟩, ⟨11, 11, 35, 5, 5, 19, false, false, false⟩, ⟨19, 30, 26, 8, 11, 23, false, false, false⟩, ⟨5, 5, 11, 11, 11, 16, false, false, false⟩, ⟨12, 16, 5, 27, 5, 1, false, false, false⟩, ⟨12, 16, 5, 34, 5, 27, false, false, false⟩, ⟨27, 28, 12, 36, 12, 21, false, false, false⟩, ⟨16, 11, 5, 28, 5, 10, false, false, false⟩, ⟨16, 11, 5, 37, 5, 28, false, false, false⟩, ⟨28, 5, 16, 38, 16, 23, false, false, false⟩, ⟨11, 11, 5, 5, 5, 37, false, false, false⟩, ⟨34, 37, 12, 11, 11, 36, false, false, false⟩, ⟨36, 38, 27, 30, 34, 42, false, false, false⟩, ⟨11, 11, 34, 5, 5, 30, false, false, false⟩, ⟨30, 33, 36, 11, 11, 11, false, false, false⟩, ⟨37, 5, 16, 11, 11, 38, false, false, false⟩],
  #[⟨38, 11, 28, 33, 37, 43, false, false, false⟩, ⟨11, 11, 37, 5, 5, 33, false, false, false⟩, ⟨33, 5, 38, 11, 11, 11, false, false, false⟩, ⟨4, 20, 4, 4, 4, 13, false, false, false⟩, ⟨4, 21, 4, 14, 4, 4, false, false, false⟩, ⟨1, 13, 1, 1, 1, 20, false, false, false⟩, ⟨13, 39, 26, 4, 4, 22, false, false, false⟩, ⟨1, 14, 1, 21, 1, 1, false, false, false⟩, ⟨14, 42, 4, 23, 26, 4, false, false, false⟩, ⟨20, 22, 27, 1, 1, 39, false, false, false⟩, ⟨21, 23, 1, 42, 27, 1, false, false, false⟩, ⟨22, 11, 28, 10, 10, 40, false, false, false⟩, ⟨23, 11, 10, 43, 28, 10, false, false, false⟩, ⟨10, 5, 22, 41, 23, 41, false, false, false⟩, ⟨39, 40, 29, 1, 20, 11, false, false, false⟩, ⟨11, 11, 30, 15, 39, 5, false, false, false⟩],
  #[⟨1, 41, 39, 1, 1, 15, false, false, false⟩, ⟨40, 5, 32, 41, 22, 11, false, false, false⟩, ⟨11, 11, 33, 17, 40, 5, false, false, false⟩, ⟨41, 11, 40, 10, 10, 17, false, false, false⟩, ⟨17, 5, 11, 22, 41, 9, false, false, false⟩, ⟨42, 43, 21, 11, 36, 1, false, false, false⟩, ⟨1, 41, 1, 18, 42, 1, false, false, false⟩, ⟨11, 11, 42, 5, 30, 18, false, false, false⟩, ⟨43, 5, 23, 11, 38, 41, false, false, false⟩, ⟨41, 11, 10, 19, 43, 10, false, false, false⟩, ⟨11, 11, 43, 5, 33, 19, false, false, false⟩, ⟨19, 5, 41, 8, 11, 23, false, false, false⟩, ⟨1, 10, 1, 21, 1, 20, false, false, false⟩, ⟨10, 5, 41, 23, 41, 22, false, false, false⟩, ⟨5, 5, 11, 7, 11, 12, false, false, false⟩, ⟨5, 5, 11, 9, 11, 12, false, false, false⟩],
  #[⟨9, 11, 5, 2, 17, 14, false, false, false⟩, ⟨11, 11, 5, 5, 30, 18, false, false, false⟩, ⟨11, 11, 5, 5, 33, 19, false, false, false⟩, ⟨5, 5, 11, 7, 11, 6, false, false, false⟩, ⟨5, 5, 11, 9, 11, 8, false, false, false⟩, ⟨5, 5, 11, 12, 11, 6, false, false, false⟩, ⟨5, 5, 11, 12, 11, 8, false, false, false⟩, ⟨8, 11, 19, 13, 5, 2, false, false, false⟩, ⟨11, 11, 30, 15, 5, 5, false, false, false⟩, ⟨11, 11, 33, 17, 5, 5, false, false, false⟩, ⟨16, 11, 5, 13, 5, 28, false, false, false⟩, ⟨22, 11, 28, 13, 13, 40, false, false, false⟩, ⟨13, 24, 22, 4, 4, 41, false, false, false⟩, ⟨41, 11, 40, 13, 13, 17, false, false, false⟩, ⟨13, 24, 41, 4, 4, 22, false, false, false⟩, ⟨16, 11, 5, 28, 5, 14, false, false, false⟩],
  #[⟨23, 11, 14, 43, 28, 14, false, false, false⟩, ⟨14, 34, 4, 41, 23, 4, false, false, false⟩, ⟨41, 11, 14, 19, 43, 14, false, false, false⟩, ⟨14, 34, 4, 23, 41, 4, false, false, false⟩, ⟨4, 27, 4, 4, 4, 26, false, false, false⟩, ⟨11, 11, 5, 24, 24, 5, false, false, false⟩, ⟨1, 4, 24, 1, 1, 24, false, false, false⟩, ⟨24, 25, 11, 1, 1, 11, false, false, false⟩, ⟨25, 24, 11, 4, 12, 11, false, false, false⟩, ⟨11, 11, 5, 25, 25, 5, false, false, false⟩, ⟨4, 1, 25, 4, 4, 25, false, false, false⟩, ⟨25, 24, 11, 4, 4, 11, false, false, false⟩, ⟨25, 24, 11, 26, 4, 11, false, false, false⟩, ⟨11, 11, 5, 31, 25, 5, false, false, false⟩, ⟨1, 26, 24, 27, 1, 24, false, false, false⟩, ⟨1, 26, 1, 1, 1, 27, false, false, false⟩],
  #[⟨27, 28, 1, 20, 1, 29, false, false, false⟩, ⟨4, 1, 4, 26, 4, 26, false, false, false⟩, ⟨26, 44, 25, 28, 4, 31, false, false, false⟩, ⟨26, 29, 4, 13, 4, 28, false, false, false⟩, ⟨28, 30, 26, 22, 26, 32, false, false, false⟩, ⟨24, 31, 11, 29, 1, 11, false, false, false⟩, ⟨31, 30, 11, 32, 26, 11, false, false, false⟩, ⟨1, 26, 1, 27, 1, 1, false, false, false⟩, ⟨4, 1, 12, 26, 12, 26, false, false, false⟩, ⟨26, 36, 4, 28, 4, 14, false, false, false⟩, ⟨1, 10, 12, 29, 12, 36, false, false, false⟩, ⟨36, 38, 27, 30, 1, 42, false, false, false⟩, ⟨29, 32, 1, 39, 27, 30, false, false, false⟩, ⟨30, 33, 36, 11, 29, 11, false, false, false⟩, ⟨10, 5, 16, 32, 16, 38, false, false, false⟩, ⟨38, 11, 28, 33, 10, 43, false, false, false⟩],
  #[⟨32, 11, 10, 40, 28, 33, false, false, false⟩, ⟨33, 5, 38, 11, 32, 11, false, false, false⟩, ⟨24, 25, 11, 44, 1, 11, false, false, false⟩, ⟨4, 21, 25, 14, 4, 25, false, false, false⟩, ⟨25, 24, 11, 45, 4, 11, false, false, false⟩, ⟨11, 11, 5, 33, 25, 5, false, false, false⟩, ⟨1, 14, 1, 29, 1, 44, false, false, false⟩, ⟨44, 45, 24, 30, 1, 30, false, false, false⟩, ⟨30, 33, 44, 11, 29, 11, false, false, false⟩, ⟨14, 42, 4, 32, 26, 45, false, false, false⟩, ⟨45, 44, 25, 33, 14, 33, false, false, false⟩, ⟨32, 11, 14, 40, 28, 33, false, false, false⟩, ⟨33, 30, 45, 11, 32, 11, false, false, false⟩, ⟨30, 33, 11, 11, 44, 11, false, false, false⟩, ⟨11, 11, 5, 5, 30, 5, false, false, false⟩, ⟨11, 11, 30, 5, 30, 5, false, false, false⟩],
  #[⟨33, 30, 11, 11, 45, 11, false, false, false⟩, ⟨11, 11, 5, 5, 33, 5, false, false, false⟩, ⟨11, 11, 33, 5, 33, 5, false, false, false⟩, ⟨24, 31, 11, 21, 12, 11, false, false, false⟩, ⟨21, 23, 24, 42, 27, 24, false, false, false⟩, ⟨24, 31, 11, 44, 21, 11, false, false, false⟩, ⟨31, 5, 11, 23, 16, 11, false, false, false⟩, ⟨11, 11, 5, 31, 31, 5, false, false, false⟩, ⟨23, 11, 31, 43, 28, 31, false, false, false⟩, ⟨31, 5, 11, 46, 23, 11, false, false, false⟩, ⟨42, 43, 21, 11, 36, 44, false, false, false⟩, ⟨44, 46, 24, 30, 42, 30, false, false, false⟩, ⟨11, 11, 42, 5, 30, 30, false, false, false⟩, ⟨30, 33, 44, 11, 11, 11, false, false, false⟩, ⟨43, 5, 23, 11, 38, 46, false, false, false⟩, ⟨46, 11, 31, 33, 43, 33, false, false, false⟩],
  #[⟨11, 11, 43, 5, 33, 33, false, false, false⟩, ⟨33, 5, 46, 11, 11, 11, false, false, false⟩, ⟨33, 5, 11, 11, 46, 11, false, false, false⟩, ⟨4, 27, 4, 26, 4, 4, false, false, false⟩, ⟨1, 4, 1, 34, 34, 1, false, false, false⟩, ⟨11, 11, 34, 5, 5, 34, false, false, false⟩, ⟨34, 35, 1, 11, 11, 1, false, false, false⟩, ⟨35, 34, 12, 11, 11, 4, false, false, false⟩, ⟨4, 1, 4, 35, 35, 4, false, false, false⟩, ⟨11, 11, 35, 5, 5, 35, false, false, false⟩, ⟨35, 34, 4, 11, 11, 4, false, false, false⟩, ⟨35, 34, 4, 11, 11, 26, false, false, false⟩, ⟨1, 26, 1, 34, 34, 27, false, false, false⟩, ⟨27, 28, 1, 36, 1, 21, false, false, false⟩, ⟨26, 44, 4, 37, 35, 28, false, false, false⟩, ⟨28, 30, 26, 38, 26, 23, false, false, false⟩],
  #[⟨11, 11, 35, 5, 5, 37, false, false, false⟩, ⟨34, 37, 1, 11, 11, 36, false, false, false⟩, ⟨37, 30, 26, 11, 11, 38, false, false, false⟩, ⟨34, 35, 1, 11, 11, 44, false, false, false⟩, ⟨4, 20, 4, 35, 35, 13, false, false, false⟩, ⟨35, 34, 4, 11, 11, 45, false, false, false⟩, ⟨1, 13, 1, 44, 1, 36, false, false, false⟩, ⟨44, 45, 1, 30, 34, 30, false, false, false⟩, ⟨30, 33, 36, 11, 44, 11, false, false, false⟩, ⟨13, 39, 26, 45, 4, 38, false, false, false⟩, ⟨38, 11, 28, 33, 13, 43, false, false, false⟩, ⟨45, 44, 13, 33, 35, 33, false, false, false⟩, ⟨33, 30, 38, 11, 45, 11, false, false, false⟩, ⟨11, 11, 35, 5, 5, 33, false, false, false⟩, ⟨11, 11, 30, 5, 5, 5, false, false, false⟩, ⟨33, 30, 45, 11, 11, 11, false, false, false⟩],
  #[⟨11, 11, 33, 5, 5, 5, false, false, false⟩, ⟨34, 37, 12, 11, 11, 20, false, false, false⟩, ⟨20, 22, 27, 34, 34, 39, false, false, false⟩, ⟨34, 37, 20, 11, 11, 44, false, false, false⟩, ⟨37, 5, 16, 11, 11, 22, false, false, false⟩, ⟨22, 11, 28, 37, 37, 40, false, false, false⟩, ⟨11, 11, 37, 5, 5, 37, false, false, false⟩, ⟨37, 5, 22, 11, 11, 46, false, false, false⟩, ⟨39, 40, 29, 44, 20, 11, false, false, false⟩, ⟨11, 11, 30, 30, 39, 5, false, false, false⟩, ⟨44, 46, 39, 30, 34, 30, false, false, false⟩, ⟨40, 5, 32, 46, 22, 11, false, false, false⟩, ⟨11, 11, 33, 33, 40, 5, false, false, false⟩, ⟨46, 11, 40, 33, 37, 33, false, false, false⟩, ⟨11, 11, 30, 24, 39, 5, false, false, false⟩, ⟨1, 3, 39, 1, 1, 24, false, false, false⟩],
  #[⟨40, 5, 32, 3, 22, 11, false, false, false⟩, ⟨11, 11, 33, 25, 40, 5, false, false, false⟩, ⟨3, 7, 40, 4, 13, 25, false, false, false⟩, ⟨25, 24, 11, 4, 3, 11, false, false, false⟩, ⟨5, 5, 11, 7, 11, 11, false, false, false⟩, ⟨11, 11, 30, 24, 5, 5, false, false, false⟩, ⟨7, 9, 5, 0, 15, 24, false, false, false⟩, ⟨24, 31, 11, 1, 7, 11, false, false, false⟩, ⟨5, 5, 11, 9, 11, 11, false, false, false⟩, ⟨11, 11, 33, 31, 5, 5, false, false, false⟩, ⟨9, 11, 5, 2, 17, 31, false, false, false⟩, ⟨31, 5, 11, 41, 9, 11, false, false, false⟩, ⟨1, 41, 24, 27, 0, 24, false, false, false⟩, ⟨1, 41, 0, 1, 1, 27, false, false, false⟩, ⟨2, 5, 9, 41, 22, 41, false, false, false⟩, ⟨41, 11, 31, 28, 2, 31, false, false, false⟩],
  #[⟨41, 11, 2, 10, 10, 28, false, false, false⟩, ⟨28, 5, 41, 22, 41, 32, false, false, false⟩, ⟨31, 5, 11, 32, 41, 11, false, false, false⟩, ⟨1, 3, 1, 34, 42, 1, false, false, false⟩, ⟨11, 11, 42, 5, 30, 34, false, false, false⟩, ⟨43, 5, 23, 11, 38, 3, false, false, false⟩, ⟨3, 6, 14, 35, 43, 4, false, false, false⟩, ⟨11, 11, 43, 5, 33, 35, false, false, false⟩, ⟨35, 34, 3, 11, 11, 4, false, false, false⟩, ⟨5, 5, 11, 11, 11, 6, false, false, false⟩, ⟨6, 8, 18, 34, 5, 0, false, false, false⟩, ⟨11, 11, 5, 5, 30, 34, false, false, false⟩, ⟨34, 37, 6, 11, 11, 1, false, false, false⟩, ⟨5, 5, 11, 11, 11, 8, false, false, false⟩, ⟨8, 11, 19, 37, 5, 2, false, false, false⟩, ⟨11, 11, 5, 5, 33, 37, false, false, false⟩],
  #[⟨37, 5, 8, 11, 11, 41, false, false, false⟩, ⟨1, 41, 1, 27, 0, 1, false, false, false⟩, ⟨1, 41, 0, 34, 34, 27, false, false, false⟩, ⟨2, 5, 23, 41, 8, 41, false, false, false⟩, ⟨41, 11, 10, 28, 2, 10, false, false, false⟩, ⟨41, 11, 2, 37, 37, 28, false, false, false⟩, ⟨28, 5, 41, 38, 41, 23, false, false, false⟩, ⟨37, 5, 41, 11, 11, 38, false, false, false⟩, ⟨41, 11, 2, 13, 13, 28, false, false, false⟩, ⟨41, 11, 14, 28, 2, 14, false, false, false⟩, ⟨26, 44, 4, 10, 4, 28, false, false, false⟩, ⟨26, 44, 4, 28, 4, 10, false, false, false⟩, ⟨1, 10, 1, 29, 1, 36, false, false, false⟩, ⟨10, 30, 26, 32, 26, 38, false, false, false⟩, ⟨24, 31, 11, 21, 1, 11, false, false, false⟩, ⟨31, 30, 11, 23, 26, 11, false, false, false⟩],
  #[⟨1, 4, 1, 44, 1, 44, false, false, false⟩, ⟨4, 1, 4, 45, 4, 45, false, false, false⟩, ⟨44, 45, 1, 30, 1, 30, false, false, false⟩, ⟨45, 44, 13, 33, 4, 33, false, false, false⟩, ⟨45, 44, 4, 33, 14, 33, false, false, false⟩, ⟨30, 33, 44, 11, 44, 11, false, false, false⟩, ⟨33, 30, 45, 11, 45, 11, false, false, false⟩, ⟨1, 10, 20, 44, 21, 44, false, false, false⟩, ⟨10, 5, 22, 46, 23, 46, false, false, false⟩, ⟨44, 46, 39, 30, 1, 30, false, false, false⟩, ⟨46, 11, 40, 33, 10, 33, false, false, false⟩, ⟨44, 46, 1, 30, 42, 30, false, false, false⟩, ⟨46, 11, 10, 33, 43, 33, false, false, false⟩, ⟨33, 5, 46, 11, 46, 11, false, false, false⟩, ⟨45, 44, 25, 33, 4, 33, false, false, false⟩, ⟨45, 44, 4, 33, 4, 33, false, false, false⟩],
  #[⟨1, 14, 1, 44, 21, 44, false, false, false⟩, ⟨14, 34, 4, 46, 23, 45, false, false, false⟩, ⟨46, 11, 14, 33, 43, 33, false, false, false⟩, ⟨33, 30, 45, 11, 46, 11, false, false, false⟩, ⟨4, 1, 25, 14, 14, 25, false, false, false⟩, ⟨4, 21, 25, 4, 14, 25, false, false, false⟩, ⟨24, 31, 11, 1, 21, 11, false, false, false⟩, ⟨31, 5, 11, 41, 23, 11, false, false, false⟩, ⟨1, 41, 24, 18, 42, 24, false, false, false⟩, ⟨41, 11, 31, 19, 43, 31, false, false, false⟩, ⟨21, 23, 24, 0, 18, 24, false, false, false⟩, ⟨31, 5, 11, 23, 41, 11, false, false, false⟩, ⟨23, 11, 31, 2, 19, 31, false, false, false⟩, ⟨35, 34, 3, 11, 11, 45, false, false, false⟩, ⟨4, 0, 4, 45, 3, 45, false, false, false⟩, ⟨45, 44, 4, 33, 35, 33, false, false, false⟩],
  #[⟨34, 37, 6, 11, 11, 44, false, false, false⟩, ⟨37, 5, 8, 11, 11, 46, false, false, false⟩, ⟨0, 2, 21, 44, 6, 44, false, false, false⟩, ⟨44, 46, 24, 30, 0, 30, false, false, false⟩, ⟨44, 46, 0, 30, 34, 30, false, false, false⟩, ⟨2, 5, 23, 46, 8, 46, false, false, false⟩, ⟨46, 11, 31, 33, 2, 33, false, false, false⟩, ⟨46, 11, 2, 33, 37, 33, false, false, false⟩, ⟨34, 37, 1, 11, 11, 20, false, false, false⟩, ⟨37, 30, 26, 11, 11, 22, false, false, false⟩, ⟨1, 13, 20, 44, 1, 44, false, false, false⟩, ⟨13, 24, 22, 45, 4, 46, false, false, false⟩, ⟨46, 11, 40, 33, 13, 33, false, false, false⟩, ⟨33, 30, 46, 11, 45, 11, false, false, false⟩, ⟨4, 1, 13, 35, 35, 13, false, false, false⟩, ⟨4, 20, 13, 35, 35, 4, false, false, false⟩],
  #[⟨34, 37, 20, 11, 11, 1, false, false, false⟩, ⟨37, 5, 22, 11, 11, 41, false, false, false⟩, ⟨1, 41, 39, 34, 34, 15, false, false, false⟩, ⟨41, 11, 40, 37, 37, 17, false, false, false⟩, ⟨20, 22, 15, 34, 34, 0, false, false, false⟩, ⟨37, 5, 41, 11, 11, 22, false, false, false⟩, ⟨22, 11, 17, 37, 37, 2, false, false, false⟩, ⟨25, 24, 11, 45, 3, 11, false, false, false⟩, ⟨4, 0, 3, 45, 4, 45, false, false, false⟩, ⟨24, 31, 11, 44, 7, 11, false, false, false⟩, ⟨31, 5, 11, 46, 9, 11, false, false, false⟩, ⟨0, 2, 7, 44, 20, 44, false, false, false⟩, ⟨2, 5, 9, 46, 22, 46, false, false, false⟩, ⟨31, 5, 11, 3, 9, 11, false, false, false⟩, ⟨11, 11, 5, 25, 31, 5, false, false, false⟩, ⟨1, 3, 24, 1, 0, 24, false, false, false⟩],
  #[⟨3, 12, 31, 4, 2, 25, false, false, false⟩, ⟨12, 12, 5, 14, 5, 25, false, false, false⟩, ⟨12, 16, 5, 18, 5, 24, false, false, false⟩, ⟨16, 11, 5, 19, 5, 31, false, false, false⟩, ⟨10, 5, 8, 41, 9, 41, false, false, false⟩, ⟨10, 5, 41, 32, 41, 38, false, false, false⟩, ⟨37, 5, 8, 11, 11, 3, false, false, false⟩, ⟨1, 3, 0, 34, 34, 1, false, false, false⟩, ⟨3, 12, 2, 35, 37, 4, false, false, false⟩, ⟨11, 11, 37, 5, 5, 35, false, false, false⟩, ⟨12, 12, 5, 35, 5, 13, false, false, false⟩, ⟨12, 16, 5, 34, 5, 15, false, false, false⟩, ⟨16, 11, 5, 37, 5, 17, false, false, false⟩, ⟨10, 30, 26, 23, 26, 22, false, false, false⟩, ⟨44, 46, 0, 30, 1, 30, false, false, false⟩, ⟨46, 11, 2, 33, 10, 33, false, false, false⟩],
  #[⟨44, 46, 1, 30, 0, 30, false, false, false⟩, ⟨46, 11, 10, 33, 2, 33, false, false, false⟩, ⟨46, 11, 14, 33, 2, 33, false, false, false⟩, ⟨4, 1, 3, 45, 3, 45, false, false, false⟩, ⟨1, 10, 6, 44, 7, 44, false, false, false⟩, ⟨10, 5, 8, 46, 9, 46, false, false, false⟩, ⟨46, 11, 2, 33, 13, 33, false, false, false⟩, ⟨31, 5, 11, 3, 23, 11, false, false, false⟩, ⟨37, 5, 22, 11, 11, 3, false, false, false⟩]]

def links : Array (Array (Array ℕ)) := #[
  #[#[0, 1, 2, 3, 4, 5, 6, 7], #[8, 8, 3, 3, 9, 10, 11, 11], #[12, 3, 12, 3, 13, 11, 14, 11], #[3, 3, 3, 3, 11, 11, 11, 11], #[15, 16, 17, 18, 19, 20, 21, 22], #[23, 24, 25, 26, 27, 5, 28, 7], #[29, 30, 31, 26, 32, 33, 6, 7], #[26, 26, 26, 26, 7, 11, 11, 11], #[8, 8, 3, 3, 10, 10, 11, 11], #[34, 34, 26, 26, 9, 10, 11, 11], #[34, 34, 26, 26, 10, 10, 11, 11], #[26, 26, 26, 26, 11, 11, 11, 11], #[12, 3, 12, 3, 14, 11, 14, 11], #[35, 26, 35, 26, 13, 11, 14, 11], #[35, 26, 35, 26, 14, 11, 14, 11], #[36, 37, 38, 39, 36, 37, 38, 39]],
  #[#[40, 16, 41, 42, 43, 44, 45, 46], #[47, 41, 17, 48, 49, 50, 51, 52], #[53, 26, 26, 26, 54, 55, 56, 11], #[36, 37, 38, 39, 36, 37, 38, 57], #[58, 59, 60, 61, 62, 63, 64, 65], #[66, 67, 68, 69, 70, 71, 72, 73], #[74, 75, 76, 77, 78, 79, 80, 81], #[23, 24, 25, 26, 27, 5, 82, 7], #[34, 34, 26, 26, 9, 10, 11, 11], #[26, 26, 26, 26, 83, 11, 11, 11], #[26, 26, 26, 26, 11, 11, 11, 11], #[84, 16, 85, 18, 86, 20, 87, 22], #[88, 30, 25, 26, 89, 33, 28, 7], #[29, 30, 31, 26, 32, 90, 6, 7], #[26, 26, 26, 26, 91, 11, 11, 11], #[35, 26, 35, 26, 13, 11, 14, 11]],
  #[#[92, 93, 17, 18, 94, 95, 21, 22], #[96, 30, 25, 26, 97, 33, 28, 7], #[34, 34, 26, 26, 10, 10, 11, 11], #[35, 26, 35, 26, 14, 11, 14, 11], #[36, 37, 38, 98, 36, 37, 38, 98], #[99, 37, 100, 98, 99, 37, 100, 98], #[101, 100, 38, 98, 101, 100, 38, 98], #[98, 100, 100, 39, 98, 100, 100, 39], #[99, 37, 100, 39, 99, 37, 100, 39], #[39, 41, 41, 53, 39, 102, 102, 54], #[53, 26, 26, 26, 54, 55, 11, 11], #[99, 37, 100, 39, 99, 37, 100, 103], #[58, 59, 60, 61, 62, 63, 104, 65], #[39, 41, 41, 53, 39, 45, 102, 54], #[105, 75, 26, 106, 107, 108, 109, 110], #[101, 100, 38, 39, 101, 100, 38, 39]],
  #[#[53, 26, 26, 26, 54, 11, 56, 11], #[101, 100, 38, 39, 101, 100, 38, 111], #[39, 41, 41, 53, 39, 102, 50, 54], #[66, 67, 68, 69, 70, 112, 72, 73], #[113, 26, 76, 114, 115, 116, 117, 118], #[53, 26, 26, 26, 54, 11, 11, 11], #[53, 26, 26, 26, 54, 11, 11, 11], #[26, 26, 26, 26, 11, 55, 11, 11], #[26, 26, 26, 26, 11, 11, 56, 11], #[98, 100, 100, 39, 98, 100, 100, 57], #[99, 37, 100, 119, 99, 37, 100, 119], #[99, 37, 120, 98, 99, 37, 121, 98], #[39, 122, 41, 53, 39, 123, 102, 124], #[125, 126, 127, 128, 129, 130, 131, 132], #[99, 37, 100, 119, 99, 37, 100, 133], #[99, 37, 120, 98, 99, 37, 134, 98]],
  #[#[39, 135, 136, 137, 57, 138, 139, 140], #[141, 142, 143, 144, 145, 146, 147, 148], #[101, 100, 38, 149, 101, 100, 38, 149], #[39, 41, 150, 53, 39, 102, 151, 152], #[101, 153, 38, 98, 101, 154, 38, 98], #[155, 156, 157, 158, 159, 160, 161, 162], #[101, 100, 38, 149, 101, 100, 38, 163], #[39, 164, 165, 166, 57, 167, 168, 169], #[101, 153, 38, 98, 101, 170, 38, 98], #[171, 172, 173, 174, 175, 176, 177, 178], #[53, 26, 26, 26, 54, 179, 180, 11], #[181, 75, 26, 106, 182, 108, 109, 110], #[183, 26, 76, 114, 184, 116, 117, 118], #[26, 26, 26, 26, 11, 55, 56, 11], #[74, 185, 186, 77, 78, 187, 188, 189], #[190, 191, 192, 128, 193, 194, 195, 196]],
  #[#[197, 198, 199, 158, 200, 201, 202, 203], #[204, 75, 76, 77, 205, 79, 80, 81], #[88, 30, 25, 26, 89, 33, 82, 7], #[26, 26, 26, 26, 83, 11, 11, 11], #[99, 37, 100, 39, 99, 37, 100, 39], #[206, 41, 85, 48, 207, 50, 208, 52], #[99, 37, 100, 39, 99, 37, 100, 57], #[149, 67, 209, 69, 163, 71, 210, 73], #[88, 30, 25, 26, 89, 90, 82, 7], #[211, 93, 85, 18, 212, 95, 87, 22], #[96, 30, 25, 26, 97, 90, 28, 7], #[26, 26, 26, 26, 91, 11, 11, 11], #[101, 100, 38, 39, 101, 100, 38, 39], #[213, 93, 41, 42, 214, 215, 45, 46], #[101, 100, 38, 39, 101, 100, 38, 57], #[119, 216, 60, 61, 133, 217, 64, 65]],
  #[#[96, 30, 25, 26, 97, 90, 82, 7], #[211, 93, 85, 18, 212, 95, 87, 22], #[98, 100, 100, 98, 98, 100, 100, 98], #[99, 37, 100, 98, 99, 37, 100, 98], #[98, 100, 100, 98, 98, 100, 100, 98], #[101, 100, 38, 98, 101, 100, 38, 98], #[39, 41, 41, 53, 39, 102, 102, 54], #[98, 100, 100, 39, 98, 100, 100, 103], #[39, 135, 136, 137, 57, 138, 218, 140], #[53, 26, 26, 26, 54, 179, 11, 11], #[26, 26, 26, 26, 11, 55, 11, 11], #[105, 185, 26, 106, 107, 219, 109, 220], #[190, 191, 192, 128, 193, 194, 221, 196], #[26, 26, 26, 26, 11, 109, 11, 11], #[181, 75, 26, 106, 222, 108, 109, 110], #[98, 100, 100, 39, 98, 100, 100, 111]],
  #[#[39, 164, 165, 166, 57, 223, 168, 169], #[53, 26, 26, 26, 54, 11, 180, 11], #[26, 26, 26, 26, 11, 11, 56, 11], #[113, 26, 186, 114, 115, 116, 224, 225], #[26, 26, 26, 26, 11, 11, 116, 11], #[197, 198, 199, 158, 200, 226, 202, 203], #[183, 26, 76, 114, 227, 116, 117, 118], #[98, 100, 100, 119, 98, 100, 100, 119], #[98, 100, 120, 98, 98, 100, 121, 98], #[98, 100, 120, 98, 98, 100, 121, 98], #[39, 122, 41, 53, 39, 123, 102, 54], #[39, 122, 41, 53, 39, 123, 102, 54], #[53, 26, 26, 26, 54, 11, 11, 228], #[125, 229, 230, 231, 232, 233, 234, 235], #[98, 100, 229, 98, 98, 100, 233, 98], #[26, 230, 26, 26, 11, 234, 11, 228]],
  #[#[231, 126, 127, 128, 236, 130, 131, 132], #[125, 229, 230, 231, 232, 233, 234, 236], #[98, 100, 229, 98, 98, 100, 237, 98], #[26, 238, 239, 240, 241, 242, 243, 244], #[245, 142, 143, 144, 246, 146, 147, 148], #[98, 100, 100, 119, 98, 100, 100, 133], #[98, 100, 120, 98, 98, 100, 134, 98], #[39, 122, 41, 53, 39, 123, 102, 152], #[39, 41, 41, 53, 39, 102, 102, 124], #[53, 247, 239, 240, 248, 249, 243, 244], #[39, 135, 136, 166, 57, 138, 139, 169], #[39, 164, 136, 137, 57, 167, 139, 140], #[250, 251, 252, 253, 254, 255, 256, 257], #[125, 229, 230, 258, 232, 233, 259, 260], #[98, 100, 142, 98, 98, 100, 261, 98], #[262, 263, 252, 264, 265, 266, 267, 268]],
  #[#[269, 270, 271, 98, 272, 273, 274, 98], #[275, 229, 276, 277, 278, 279, 280, 281], #[98, 100, 142, 98, 98, 100, 146, 98], #[282, 283, 284, 285, 286, 287, 288, 289], #[269, 270, 271, 98, 290, 273, 274, 98], #[98, 100, 100, 149, 98, 100, 100, 149], #[39, 41, 150, 53, 39, 102, 151, 54], #[39, 41, 150, 53, 39, 102, 151, 54], #[53, 26, 26, 26, 54, 11, 11, 291], #[98, 153, 100, 98, 98, 154, 100, 98], #[98, 153, 100, 98, 98, 154, 100, 98], #[155, 292, 293, 294, 295, 296, 297, 298], #[26, 26, 292, 26, 11, 11, 296, 291], #[98, 293, 100, 98, 98, 297, 100, 98], #[294, 156, 157, 158, 299, 160, 161, 162], #[155, 292, 293, 294, 295, 296, 297, 299]],
  #[#[26, 247, 300, 301, 241, 249, 302, 303], #[98, 293, 100, 98, 98, 304, 100, 98], #[305, 172, 173, 174, 306, 176, 177, 178], #[98, 100, 100, 149, 98, 100, 100, 163], #[39, 41, 41, 53, 39, 102, 102, 152], #[39, 41, 150, 53, 39, 102, 151, 124], #[53, 247, 239, 301, 248, 249, 243, 303], #[39, 164, 136, 166, 57, 167, 139, 169], #[39, 164, 165, 137, 57, 167, 168, 140], #[250, 251, 252, 253, 254, 255, 256, 257], #[98, 153, 100, 98, 98, 170, 100, 98], #[155, 292, 293, 307, 295, 308, 297, 309], #[310, 251, 311, 312, 313, 314, 315, 316], #[98, 173, 100, 98, 98, 317, 100, 98], #[285, 271, 318, 98, 319, 274, 320, 98], #[321, 322, 293, 323, 324, 325, 326, 327]],
  #[#[328, 329, 330, 269, 331, 332, 333, 290], #[98, 173, 100, 98, 98, 177, 100, 98], #[285, 271, 318, 98, 289, 274, 320, 98], #[26, 26, 26, 26, 11, 179, 11, 11], #[26, 26, 26, 26, 11, 11, 180, 11], #[26, 26, 26, 26, 11, 179, 11, 11], #[181, 185, 26, 106, 182, 219, 109, 220], #[26, 26, 26, 26, 11, 11, 180, 11], #[183, 26, 186, 114, 184, 116, 224, 225], #[181, 185, 26, 106, 182, 219, 109, 110], #[183, 26, 186, 114, 184, 116, 224, 118], #[190, 191, 192, 128, 193, 194, 195, 196], #[197, 198, 199, 158, 200, 201, 202, 203], #[204, 75, 76, 77, 205, 79, 80, 189], #[190, 334, 335, 231, 336, 337, 338, 339], #[98, 100, 229, 98, 98, 100, 233, 98]],
  #[#[26, 230, 26, 26, 83, 234, 11, 228], #[340, 341, 342, 343, 344, 345, 346, 347], #[98, 100, 229, 98, 98, 100, 279, 98], #[88, 348, 349, 240, 350, 351, 352, 353], #[245, 142, 143, 144, 354, 146, 147, 148], #[197, 355, 356, 294, 357, 358, 359, 360], #[26, 26, 292, 26, 91, 11, 296, 291], #[98, 293, 100, 98, 98, 297, 100, 98], #[361, 362, 363, 364, 365, 366, 367, 368], #[96, 369, 370, 301, 371, 372, 373, 374], #[98, 293, 100, 98, 98, 326, 100, 98], #[305, 172, 173, 174, 375, 176, 177, 178], #[26, 26, 26, 26, 11, 179, 180, 11], #[204, 185, 186, 77, 205, 187, 188, 189], #[98, 100, 100, 39, 98, 100, 100, 39], #[98, 100, 100, 39, 98, 100, 100, 111]],
  #[#[149, 67, 209, 69, 163, 112, 210, 73], #[98, 153, 100, 98, 98, 154, 100, 98], #[98, 153, 100, 98, 98, 170, 100, 98], #[98, 100, 100, 39, 98, 100, 100, 39], #[98, 100, 100, 39, 98, 100, 100, 57], #[98, 100, 100, 39, 98, 100, 100, 39], #[98, 100, 100, 39, 98, 100, 100, 103], #[119, 216, 60, 61, 133, 217, 104, 65], #[98, 100, 120, 98, 98, 100, 121, 98], #[98, 100, 120, 98, 98, 100, 134, 98], #[39, 164, 136, 137, 57, 167, 218, 140], #[190, 191, 192, 128, 193, 194, 221, 196], #[181, 75, 26, 106, 222, 108, 109, 220], #[88, 348, 349, 240, 350, 351, 376, 353], #[181, 185, 26, 106, 222, 219, 109, 220], #[39, 164, 136, 166, 57, 223, 139, 169]],
  #[#[197, 198, 199, 158, 200, 226, 202, 203], #[183, 26, 76, 114, 227, 116, 117, 225], #[96, 369, 370, 301, 371, 377, 373, 374], #[183, 26, 186, 114, 227, 116, 224, 225], #[26, 26, 26, 26, 11, 11, 11, 228], #[98, 100, 229, 98, 98, 100, 233, 98], #[26, 230, 26, 26, 11, 234, 11, 11], #[231, 229, 230, 231, 235, 233, 234, 235], #[125, 229, 230, 231, 232, 233, 234, 235], #[98, 100, 229, 98, 98, 100, 233, 98], #[26, 230, 26, 26, 11, 234, 11, 11], #[231, 229, 230, 231, 235, 233, 234, 235], #[231, 229, 230, 231, 235, 233, 234, 236], #[98, 100, 229, 98, 98, 100, 237, 98], #[26, 230, 26, 26, 11, 234, 11, 291], #[26, 26, 26, 26, 11, 11, 11, 228]],
  #[#[26, 247, 239, 240, 241, 249, 243, 244], #[26, 26, 26, 26, 11, 11, 11, 241], #[26, 238, 239, 301, 241, 242, 378, 303], #[26, 247, 239, 240, 241, 379, 243, 244], #[380, 251, 252, 253, 381, 255, 256, 257], #[231, 229, 230, 258, 235, 233, 259, 260], #[382, 229, 276, 277, 383, 279, 280, 281], #[26, 26, 26, 26, 11, 11, 11, 291], #[53, 26, 26, 26, 54, 11, 11, 241], #[26, 247, 239, 301, 241, 249, 378, 303], #[53, 26, 26, 384, 54, 179, 180, 385], #[310, 251, 386, 312, 313, 314, 387, 316], #[262, 386, 252, 264, 265, 388, 267, 268], #[389, 271, 271, 98, 390, 274, 274, 98], #[74, 185, 186, 391, 78, 187, 188, 392], #[328, 329, 393, 269, 331, 332, 394, 290]],
  #[#[282, 395, 284, 285, 286, 396, 288, 289], #[389, 271, 271, 98, 397, 274, 274, 98], #[231, 229, 230, 258, 235, 233, 234, 260], #[26, 230, 26, 26, 11, 234, 180, 11], #[231, 229, 230, 258, 235, 233, 234, 260], #[98, 100, 142, 98, 98, 100, 261, 98], #[26, 26, 26, 384, 11, 11, 180, 385], #[384, 263, 386, 389, 385, 398, 399, 390], #[389, 271, 271, 98, 390, 274, 274, 98], #[183, 26, 186, 400, 184, 116, 224, 401], #[384, 263, 386, 389, 385, 398, 388, 390], #[282, 395, 284, 285, 286, 402, 288, 289], #[389, 271, 271, 98, 403, 274, 274, 98], #[269, 270, 271, 98, 272, 273, 274, 98], #[98, 100, 100, 98, 98, 100, 100, 98], #[98, 100, 100, 98, 98, 100, 100, 98]],
  #[#[269, 270, 271, 98, 272, 273, 274, 98], #[98, 100, 100, 98, 98, 100, 100, 98], #[98, 100, 100, 98, 98, 100, 100, 98], #[125, 229, 230, 231, 232, 233, 259, 235], #[183, 230, 186, 114, 184, 404, 224, 118], #[231, 229, 230, 258, 235, 233, 405, 260], #[275, 229, 276, 406, 278, 279, 280, 407], #[98, 100, 229, 98, 98, 100, 279, 98], #[197, 408, 199, 158, 200, 409, 202, 203], #[382, 229, 410, 277, 411, 279, 412, 281], #[197, 355, 356, 307, 357, 358, 359, 413], #[384, 263, 311, 389, 414, 398, 415, 390], #[98, 173, 100, 98, 98, 317, 100, 98], #[285, 271, 318, 98, 319, 274, 320, 98], #[361, 362, 363, 416, 365, 366, 367, 417], #[418, 419, 420, 389, 421, 422, 423, 397]],
  #[#[98, 173, 100, 98, 98, 177, 100, 98], #[285, 271, 318, 98, 289, 274, 320, 98], #[269, 270, 271, 98, 290, 273, 274, 98], #[26, 26, 26, 26, 11, 11, 11, 291], #[26, 26, 292, 26, 11, 11, 296, 11], #[98, 293, 100, 98, 98, 297, 100, 98], #[294, 292, 293, 294, 298, 296, 297, 298], #[155, 292, 293, 294, 295, 296, 297, 298], #[26, 26, 292, 26, 11, 11, 296, 11], #[98, 293, 100, 98, 98, 297, 100, 98], #[294, 292, 293, 294, 298, 296, 297, 298], #[294, 292, 293, 294, 298, 296, 297, 299], #[26, 26, 292, 26, 11, 11, 296, 228], #[26, 247, 239, 301, 241, 249, 243, 303], #[26, 247, 300, 240, 241, 379, 302, 244], #[380, 251, 252, 253, 381, 255, 256, 257]],
  #[#[98, 293, 100, 98, 98, 304, 100, 98], #[294, 292, 293, 307, 298, 308, 297, 309], #[424, 322, 293, 323, 425, 325, 326, 327], #[294, 292, 293, 307, 298, 296, 297, 309], #[26, 26, 292, 26, 11, 179, 296, 11], #[294, 292, 293, 307, 298, 296, 297, 309], #[26, 26, 26, 384, 11, 179, 11, 385], #[384, 386, 311, 389, 385, 399, 415, 390], #[389, 271, 271, 98, 390, 274, 274, 98], #[181, 185, 26, 426, 182, 219, 109, 427], #[328, 329, 393, 269, 331, 332, 428, 290], #[384, 386, 311, 389, 385, 387, 415, 390], #[389, 271, 271, 98, 429, 274, 274, 98], #[98, 173, 100, 98, 98, 317, 100, 98], #[98, 100, 100, 98, 98, 100, 100, 98], #[285, 271, 318, 98, 319, 274, 320, 98]],
  #[#[98, 100, 100, 98, 98, 100, 100, 98], #[155, 292, 293, 294, 295, 308, 297, 298], #[181, 185, 292, 106, 182, 219, 430, 110], #[294, 292, 293, 307, 298, 431, 297, 309], #[321, 322, 293, 432, 324, 325, 326, 433], #[190, 191, 434, 128, 193, 194, 435, 196], #[98, 293, 100, 98, 98, 326, 100, 98], #[424, 436, 293, 323, 437, 438, 326, 327], #[190, 334, 335, 258, 336, 337, 338, 439], #[98, 100, 142, 98, 98, 100, 261, 98], #[384, 263, 311, 389, 440, 398, 415, 390], #[340, 341, 342, 441, 344, 345, 346, 442], #[98, 100, 142, 98, 98, 100, 146, 98], #[443, 419, 420, 389, 444, 422, 423, 397], #[98, 100, 229, 98, 98, 100, 233, 98], #[26, 230, 26, 26, 83, 234, 11, 11]],
  #[#[340, 341, 342, 343, 344, 345, 346, 445], #[98, 100, 229, 98, 98, 100, 446, 98], #[88, 447, 25, 26, 89, 448, 82, 7], #[231, 229, 230, 231, 339, 233, 234, 235], #[98, 100, 100, 119, 98, 100, 100, 119], #[98, 100, 120, 98, 98, 100, 121, 98], #[206, 122, 85, 48, 207, 449, 208, 52], #[125, 229, 230, 231, 232, 233, 405, 235], #[98, 100, 100, 119, 98, 100, 100, 133], #[98, 100, 120, 98, 98, 100, 134, 98], #[149, 450, 209, 69, 163, 451, 210, 73], #[275, 229, 410, 406, 278, 279, 412, 407], #[26, 230, 26, 26, 91, 234, 11, 291], #[26, 26, 26, 26, 83, 11, 11, 228], #[211, 93, 85, 18, 212, 95, 87, 452], #[96, 348, 349, 301, 371, 351, 352, 374]],
  #[#[88, 369, 349, 240, 350, 372, 352, 353], #[380, 251, 252, 253, 453, 255, 256, 257], #[382, 229, 276, 277, 411, 279, 280, 281], #[26, 26, 292, 26, 91, 11, 296, 11], #[98, 293, 100, 98, 98, 297, 100, 98], #[361, 362, 363, 364, 365, 366, 367, 454], #[96, 30, 455, 26, 97, 90, 456, 7], #[98, 293, 100, 98, 98, 457, 100, 98], #[294, 292, 293, 294, 360, 296, 297, 298], #[98, 100, 100, 149, 98, 100, 100, 149], #[213, 93, 150, 42, 214, 215, 458, 46], #[98, 153, 100, 98, 98, 154, 100, 98], #[155, 292, 293, 294, 295, 431, 297, 298], #[98, 100, 100, 149, 98, 100, 100, 163], #[119, 216, 459, 61, 133, 217, 460, 65], #[98, 153, 100, 98, 98, 170, 100, 98]],
  #[#[321, 436, 293, 432, 324, 438, 326, 433], #[26, 26, 26, 26, 91, 11, 11, 291], #[26, 26, 292, 26, 83, 11, 296, 228], #[211, 93, 85, 18, 212, 95, 87, 452], #[96, 369, 349, 301, 371, 372, 352, 374], #[88, 369, 370, 240, 350, 372, 373, 353], #[380, 251, 252, 253, 453, 255, 256, 257], #[424, 322, 293, 323, 437, 325, 326, 327], #[88, 369, 349, 240, 350, 372, 376, 353], #[96, 369, 349, 301, 371, 377, 352, 374], #[26, 247, 239, 240, 241, 379, 378, 244], #[26, 247, 239, 301, 241, 379, 378, 303], #[26, 26, 26, 384, 11, 179, 180, 385], #[204, 185, 186, 391, 461, 187, 188, 392], #[231, 229, 230, 231, 235, 233, 259, 235], #[382, 229, 276, 406, 383, 279, 280, 407]],
  #[#[26, 26, 26, 384, 11, 11, 11, 385], #[26, 26, 26, 384, 11, 11, 11, 385], #[384, 386, 386, 389, 385, 399, 399, 390], #[384, 386, 386, 389, 385, 387, 399, 390], #[384, 386, 386, 389, 385, 399, 388, 390], #[389, 271, 271, 98, 390, 274, 274, 98], #[389, 271, 271, 98, 390, 274, 274, 98], #[26, 26, 26, 384, 11, 55, 56, 385], #[204, 75, 76, 391, 205, 79, 80, 392], #[384, 263, 386, 389, 440, 398, 399, 390], #[443, 419, 462, 389, 444, 422, 463, 397], #[384, 386, 311, 389, 414, 399, 415, 390], #[418, 464, 420, 389, 421, 465, 423, 397], #[389, 271, 271, 98, 397, 274, 274, 98], #[384, 263, 386, 389, 385, 398, 399, 390], #[384, 386, 386, 389, 385, 399, 399, 390]],
  #[#[26, 26, 26, 384, 11, 11, 56, 385], #[183, 26, 76, 400, 227, 116, 117, 401], #[418, 464, 420, 389, 421, 466, 423, 397], #[389, 271, 271, 98, 403, 274, 274, 98], #[26, 230, 26, 26, 11, 234, 116, 11], #[26, 230, 26, 26, 11, 234, 56, 11], #[231, 229, 230, 231, 235, 233, 405, 235], #[382, 229, 410, 406, 411, 279, 412, 407], #[26, 230, 292, 26, 91, 234, 296, 291], #[96, 348, 370, 301, 371, 351, 373, 374], #[183, 230, 76, 114, 184, 404, 117, 118], #[382, 229, 276, 406, 411, 279, 280, 407], #[197, 408, 199, 158, 200, 409, 202, 203], #[294, 292, 293, 307, 360, 296, 297, 309], #[26, 26, 26, 384, 91, 11, 11, 385], #[384, 386, 311, 389, 385, 399, 415, 390]],
  #[#[155, 292, 293, 307, 295, 431, 297, 309], #[321, 436, 293, 323, 324, 438, 326, 327], #[96, 30, 25, 384, 97, 90, 82, 467], #[384, 263, 386, 389, 414, 398, 399, 390], #[384, 386, 311, 389, 440, 399, 415, 390], #[211, 93, 85, 468, 212, 95, 87, 469], #[418, 419, 462, 389, 421, 422, 463, 397], #[443, 464, 420, 389, 444, 465, 423, 397], #[294, 292, 293, 294, 298, 308, 297, 298], #[424, 322, 293, 432, 425, 325, 326, 433], #[26, 26, 26, 384, 11, 55, 11, 385], #[181, 75, 26, 426, 222, 108, 109, 427], #[443, 419, 462, 389, 444, 422, 470, 397], #[389, 271, 271, 98, 429, 274, 274, 98], #[26, 26, 292, 26, 11, 109, 296, 11], #[26, 26, 292, 26, 11, 55, 296, 11]],
  #[#[294, 292, 293, 294, 298, 431, 297, 298], #[424, 436, 293, 432, 437, 438, 326, 433], #[26, 230, 292, 26, 83, 234, 296, 228], #[88, 348, 370, 240, 350, 351, 373, 353], #[181, 75, 292, 106, 182, 108, 430, 110], #[424, 322, 293, 432, 437, 325, 326, 433], #[190, 191, 434, 128, 193, 194, 435, 196], #[231, 229, 230, 258, 339, 233, 234, 260], #[26, 26, 26, 384, 83, 11, 11, 385], #[125, 229, 230, 258, 232, 233, 405, 260], #[275, 229, 410, 277, 278, 279, 412, 281], #[88, 30, 25, 384, 89, 90, 82, 467], #[211, 93, 85, 468, 212, 95, 87, 469], #[275, 229, 410, 406, 278, 279, 412, 471], #[98, 100, 229, 98, 98, 100, 446, 98], #[26, 230, 26, 26, 91, 234, 11, 11]],
  #[#[96, 447, 25, 26, 97, 448, 28, 7], #[39, 122, 41, 53, 39, 123, 50, 54], #[39, 122, 150, 53, 39, 123, 151, 152], #[39, 135, 165, 166, 57, 138, 168, 169], #[74, 75, 76, 77, 78, 79, 80, 189], #[204, 185, 186, 391, 205, 187, 188, 392], #[321, 436, 293, 432, 324, 438, 326, 472], #[26, 26, 292, 26, 83, 11, 296, 11], #[88, 30, 455, 26, 89, 33, 456, 7], #[98, 293, 100, 98, 98, 457, 100, 98], #[39, 41, 150, 53, 39, 45, 151, 54], #[39, 122, 150, 53, 39, 123, 151, 124], #[39, 135, 165, 137, 57, 138, 168, 140], #[204, 185, 186, 77, 461, 187, 188, 189], #[384, 386, 386, 389, 440, 399, 399, 390], #[443, 464, 462, 389, 444, 465, 463, 397]],
  #[#[384, 386, 386, 389, 414, 399, 399, 390], #[418, 464, 462, 389, 421, 465, 463, 397], #[418, 464, 462, 389, 421, 466, 463, 397], #[26, 26, 26, 384, 7, 11, 11, 385], #[53, 26, 26, 384, 54, 55, 56, 385], #[74, 75, 76, 391, 78, 79, 80, 392], #[443, 464, 462, 389, 444, 465, 470, 397], #[382, 229, 410, 406, 411, 279, 412, 471], #[424, 436, 293, 432, 437, 438, 326, 472]]]

abbrev Index := Fin 473

def window (i : Index) : Local := ((windows[i.val / 16]?.getD #[])[i.val % 16]?).getD default

def link (i : Index) (t x y : Bool) : Index :=
  ⟨((((links[i.val / 16]?.getD #[])[i.val % 16]?.getD #[])[code t x y]?).getD 0) % 473,
    Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma certificate : ∀ i : Index, valid (window i) ∧
    ∀ t x y : Bool, window (link i t x y) = descend (window i) t x y := by
  decide +kernel

lemma at_origin : position 0 0 0 0 = window 0 := by decide

lemma decomposes (n : ℕ) : digit (n / 2) (n % 2 == 1) = n := by
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h <;> simp [digit, h] <;> omega

lemma covered (w t x y : ℕ) (ht : t < 2 ^ w) (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    ∃ i, position w t x y = window i := by
  induction w generalizing t x y with
  | zero =>
    simp only [pow_zero] at ht hx hy
    obtain rfl : t = 0 := by omega
    obtain rfl : x = 0 := by omega
    obtain rfl : y = 0 := by omega
    exact ⟨0, at_origin⟩
  | succ w ih =>
    simp only [pow_succ] at ht hx hy
    obtain ⟨i, hi⟩ := ih (t / 2) (x / 2) (y / 2) (by omega) (by omega) (by omega)
    refine ⟨link i (t % 2 == 1) (x % 2 == 1) (y % 2 == 1), ?_⟩
    have h := position_digit w (t / 2) (x / 2) (y / 2) (t % 2 == 1) (x % 2 == 1) (y % 2 == 1)
    rw [decomposes, decomposes, decomposes, hi, ← (certificate i).2] at h
    exact h

lemma address_stable (w t x y : ℕ) (ht : t < 2 ^ w) (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    address (w + 1) t x y = address w t x y := by
  induction w generalizing t x y with
  | zero =>
    simp only [pow_zero] at ht hx hy
    have : t = 0 := by omega
    have : x = 0 := by omega
    have : y = 0 := by omega
    subst_vars
    decide
  | succ w ih =>
    simp only [pow_succ] at ht hx hy
    change go (address (w + 1) (t / 2) (x / 2) (y / 2)) _ _ _ = go (address w _ _ _) _ _ _
    rw [ih (t / 2) (x / 2) (y / 2) (by omega) (by omega) (by omega)]

lemma address_wider (w u t x y : ℕ) (hu : w ≤ u) (ht : t < 2 ^ w) (hx : x < 2 ^ w)
    (hy : y < 2 ^ w) : address u t x y = address w t x y := by
  induction u, hu using Nat.le_induction with
  | base => rfl
  | succ u hu ih =>
    have hpow : 2 ^ w ≤ (2 : ℕ) ^ u := Nat.pow_le_pow_right (by decide) hu
    rw [address_stable u t x y (by omega) (by omega) (by omega), ih]

def value (t x y : ℕ) := lit (address (t + x + y + 1) t x y)

lemma at_width (w t x y : ℕ) (ht : t < 2 ^ w) (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    value t x y = lit (address w t x y) := by
  unfold value
  by_cases h : w ≤ t + x + y + 1
  · rw [address_wider w _ _ _ _ h ht hx hy]
  · have hb := Nat.lt_two_pow_self (n := t + x + y + 1)
    rw [address_wider (t + x + y + 1) w _ _ _ (by omega) (by omega) (by omega) (by omega)]

lemma natural_law (r t x y : ℕ) (hr : r = 131) :
    (t = 0 → value t x y = decide (x = 0 ∧ y = 0)) ∧
    value (t + 1) x y = localRule r (value t x y) (value t (prev x) y) (value t (x + 1) y)
      (value t x (prev y)) (value t x (y + 1)) := by
  let w := t + x + y + 2
  have hw : t + x + y + 2 < 2 ^ w := Nat.lt_two_pow_self
  obtain ⟨i, hi⟩ := covered w t x y (by omega) (by omega) (by omega)
  have h := (certificate i).1
  rw [← hi] at h
  simp only [valid, position] at h
  have hpow : t + x + y + 2 < 2 ^ (w + 1) := by rw [pow_succ]; omega
  have hpx : prev x ≤ x + 1 := by unfold prev; split <;> omega
  have hpy : prev y ≤ y + 1 := by unfold prev; split <;> omega
  rw [at_width (w + 1) t x y (by omega) (by omega) (by omega),
    at_width (w + 1) (t + 1) x y (by omega) (by omega) (by omega),
    at_width (w + 1) t (prev x) y (by omega) (by omega) (by omega),
    at_width (w + 1) t (x + 1) y (by omega) (by omega) (by omega),
    at_width (w + 1) t x (prev y) (by omega) (by omega) (by omega),
    at_width (w + 1) t x (y + 1) (by omega) (by omega) (by omega)]
  constructor
  · intro ht
    have h0 := h.1 (by simp [ht])
    cases x <;> cases y <;> simpa using h0
  · subst hr; exact h.2

def plane (t : ℕ) (x y : ℤ) := value t x.natAbs y.natAbs

lemma plane_zero (x y : ℤ) : plane 0 x y = decide (x = 0 ∧ y = 0) := by
  simpa [plane] using (natural_law 131 0 x.natAbs y.natAbs (rfl : 131 = 131)).1 rfl

lemma neighbors (x : ℤ) :
    ((x - 1).natAbs = prev x.natAbs ∧ (x + 1).natAbs = x.natAbs + 1) ∨
    ((x + 1).natAbs = prev x.natAbs ∧ (x - 1).natAbs = x.natAbs + 1) := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · right
    have a := Int.ofNat_natAbs_of_nonpos (show x ≤ 0 by omega)
    have b := Int.ofNat_natAbs_of_nonpos (show x + 1 ≤ 0 by omega)
    have c := Int.ofNat_natAbs_of_nonpos (show x - 1 ≤ 0 by omega)
    unfold prev; split <;> omega
  · decide
  · left
    have a := Int.natAbs_of_nonneg (show 0 ≤ x by omega)
    have b := Int.natAbs_of_nonneg (show 0 ≤ x + 1 by omega)
    have c := Int.natAbs_of_nonneg (show 0 ≤ x - 1 by omega)
    unfold prev; split <;> omega

lemma plane_step (r t : ℕ) (x y : ℤ) (hr : r = 131) :
    plane (t + 1) x y = localRule r (plane t x y) (plane t (x - 1) y) (plane t (x + 1) y)
      (plane t x (y - 1)) (plane t x (y + 1)) := by
  unfold plane
  rw [(natural_law r t x.natAbs y.natAbs hr).2]
  unfold localRule
  rcases neighbors x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases neighbors y with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rw [h1, h2, h3, h4] <;> ac_rfl

def gridRows (t : ℕ) (f : ℤ → ℤ → Bool) : List (List Bool) :=
  (List.range (2 * t + 1)).map fun (j : ℕ) =>
    (List.range (2 * t + 1)).map fun (i : ℕ) => f ((i : ℤ) - ↑t) ((j : ℤ) - ↑t)

def background (r : ℕ) : ℕ → Bool
  | 0 => false
  | t + 1 => applyRule r (background r t) (background r t) (background r t)
      (background r t) (background r t)

lemma applyRule_eq_localRule (r : ℕ) (c n s w e : Bool) :
    applyRule r c n s w e = localRule r c w e n s := by
  unfold applyRule localRule; congr 1; omega

lemma outside (r t : ℕ) (hr : r = 131) (x y : ℤ)
    (h : x < -(t : ℤ) ∨ (t : ℤ) < x ∨ y < -(t : ℤ) ∨ (t : ℤ) < y) :
    plane t x y = background r t := by
  induction t generalizing x y with
  | zero => rw [plane_zero]; simp [background]; omega
  | succ t ih =>
    simp only [Nat.cast_succ] at h
    rw [plane_step r t x y hr, ih x y (by omega), ih (x - 1) y (by omega),
      ih (x + 1) y (by omega), ih x (y - 1) (by omega), ih x (y + 1) (by omega)]
    rw [background]
    exact (applyRule_eq_localRule r _ _ _ _ _).symm

lemma getD_map_range {α : Type} (n : ℕ) (f : ℕ → α) (i : ℕ) (d : α) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD, hi]

lemma getCell_gridRows (t : ℕ) (bg : Bool) (f : ℤ → ℤ → Bool)
    (hout : ∀ u v : ℤ, u < -(t : ℤ) ∨ (t : ℤ) < u ∨ v < -(t : ℤ) ∨ (t : ℤ) < v → f u v = bg)
    (x y : ℤ) :
    getCell t (bg, gridRows t f) x y = f x y := by
  unfold getCell
  split_ifs with h
  · rcases h with ⟨hx1, hx2, hy1, hy2⟩
    have hiy : (y + ↑t).toNat < 2 * t + 1 := by omega
    have hix : (x + ↑t).toNat < 2 * t + 1 := by omega
    have hiy_eq : (((y + ↑t).toNat : ℤ) - ↑t) = y := by omega
    have hix_eq : (((x + ↑t).toNat : ℤ) - ↑t) = x := by omega
    unfold gridRows
    rw [getD_map_range _ _ _ _ hiy, getD_map_range _ _ _ _ hix, hix_eq, hiy_eq]
  · symm; apply hout; omega

lemma flatMap_pure_map {α β γ : Type} (xs : List α) (c : α → β) (f : β → γ) :
    List.map f (List.flatMap (fun a => [c a]) xs) = List.map (fun a => f (c a)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma stages (r t : ℕ) (hr : r = 131) :
    stageCfg r t = (background r t, gridRows t (plane t)) := by
  induction t with
  | zero =>
    simp [stageCfg, background, gridRows, plane_zero]
  | succ t ih =>
    rw [stageCfg, ih]
    have hg : getCell t (background r t, gridRows t (plane t)) = plane t := by
      funext x y; exact getCell_gridRows t (background r t) (plane t) (outside r t hr) x y
    dsimp only [stepCfg]
    rw [hg]
    refine Prod.ext rfl ?_
    simp only [List.bind_eq_flatMap, List.pure_def, flatMap_pure_map, gridRows]
    apply List.map_congr_left; intro iy _
    apply List.map_congr_left; intro ix _
    rw [plane_step r t _ _ hr]
    exact applyRule_eq_localRule r _ _ _ _ _

lemma count_map_range (n : ℕ) (g : ℕ → Bool) :
    (((List.range n).map g).count true : ℤ) = ∑ i ∈ Finset.range n, ((g i).toNat : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.count_append, Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil]
    push_cast
    rw [ih]
    cases g n <;> simp

lemma sum_map_range (n : ℕ) (g : ℕ → ℕ) :
    (Nat.cast (((List.range n).map g).sum) : ℤ) = ∑ i ∈ Finset.range n, (g i : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, Nat.cast_add, ih]
    simp

lemma sum_gridRows (t : ℕ) (f : ℤ → ℤ → Bool) :
    (Nat.cast (((gridRows t f).map fun row => row.count true).sum) : ℤ) =
      ∑ j ∈ Finset.range (2 * t + 1), ∑ i ∈ Finset.range (2 * t + 1),
        ((f ((i : ℤ) - ↑t) ((j : ℤ) - ↑t)).toNat : ℤ) := by
  unfold gridRows
  simp only [List.map_map, Function.comp_def]
  rw [sum_map_range]
  apply Finset.sum_congr rfl
  intro j _
  exact count_map_range (2 * t + 1) (fun i => f ((i : ℤ) - ↑t) ((j : ℤ) - ↑t))

lemma reflect_sum (t : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range (2 * t + 1), f (((i : ℤ) - ↑t).natAbs) =
      2 * (∑ i ∈ Finset.range (t + 1), f i) - f 0 := by
  rw [show 2 * t + 1 = (t + 1) + t by omega, Finset.sum_range_add]
  have h₁ : ∑ i ∈ Finset.range (t + 1), f (((i : ℤ) - ↑t).natAbs) =
      ∑ i ∈ Finset.range (t + 1), f i := by
    rw [← Finset.sum_range_reflect f (t + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    congr 1
    have := Int.ofNat_natAbs_of_nonpos (show (i : ℤ) - ↑t ≤ 0 by omega)
    omega
  rw [h₁]
  have h₂ : ∑ i ∈ Finset.range t, f ((((t + 1 + i : ℕ) : ℤ) - ↑t).natAbs) =
      ∑ i ∈ Finset.range t, f (i + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast
    rw [show (t : ℤ) + 1 + i - ↑t = ↑(i + 1 : ℕ) by omega]
    rfl
  rw [h₂]
  have := Finset.sum_range_succ' f t
  omega

def span (b : Bool) (n : ℕ) := if b then 2 ^ n else 1

def pick (b : Bool) (f : Bool → ℤ) := if b then f false + f true else f false

def mix (u v : Bool) (f : ℕ → ℤ) (q : ℕ) :=
  pick v fun y => pick u fun x => f (go q true x y)

def total (n : ℕ) (u v : Bool) (f : ℕ → ℤ) : ℤ :=
  ∑ j ∈ Finset.range (span v n), ∑ i ∈ Finset.range (span u n),
    f (address n (2 ^ n - 1) i j)

def weight (q : ℕ) : ℤ := (lit q).toNat

def count (n : ℕ) (u v : Bool) := total n u v weight

lemma paired (k : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range (2 * k), f i =
      ∑ i ∈ Finset.range k, (f (2 * i) + f (2 * i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    omega

lemma span_split (b : Bool) (n : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range (span b (n + 1)), f i =
      ∑ i ∈ Finset.range (span b n), pick b (fun bit => f (digit i bit)) := by
  cases b
  · simp [span, pick, digit]
  · simp only [span, ↓reduceIte, pick, digit, Bool.toNat_false,
      Bool.toNat_true, Nat.add_zero, pow_succ]
    rw [Nat.mul_comm, paired]

lemma total_step (n : ℕ) (u v : Bool) (f : ℕ → ℤ) :
    total (n + 1) u v f = total n u v (mix u v f) := by
  have ht : 2 ^ (n + 1) - 1 = digit (2 ^ n - 1) true := by
    have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    simp [digit, pow_succ]; omega
  unfold total
  rw [span_split v n]
  apply Finset.sum_congr rfl
  intro j _
  cases v <;> simp only [mix, pick, Bool.false_eq_true, ↓reduceIte, Finset.sum_add_distrib,
    span_split u n, ht, address_digit]
  all_goals first | rfl | rw [Finset.sum_add_distrib]

lemma small_go : ∀ q : Fin 47, ∀ t x y : Bool, go q.val t x y < 47 := by decide +kernel

lemma small_address (w t x y : ℕ) : address w t x y < 47 := by
  induction w generalizing t x y with
  | zero => change 0 < 47; decide
  | succ w ih => exact small_go ⟨_, ih (t / 2) (x / 2) (y / 2)⟩ _ _ _

def iterate (k : ℕ) (u v : Bool) : ℕ → ℤ :=
  match k with
  | 0 => weight
  | k + 1 => mix u v (iterate k u v)

def iterVec (k : ℕ) (u v : Bool) : List ℤ :=
  match k with
  | 0 => (List.range 47).map weight
  | k + 1 =>
    let prev := iterVec k u v
    (List.range 47).map (fun q => mix u v (fun s => prev.getD s 0) q)

lemma iterVec_eq (k : ℕ) (u v : Bool) :
    ∀ q < 47, (iterVec k u v).getD q 0 = iterate k u v q := by
  induction k with
  | zero =>
    intro q hq
    exact getD_map_range 47 weight q 0 hq
  | succ k ih =>
    intro q hq
    unfold iterVec iterate
    dsimp only
    rw [getD_map_range 47 _ q 0 hq]
    unfold mix
    congr 1; funext y; congr 1; funext x
    exact ih (go q true x y) (small_go ⟨q, hq⟩ true x y)

lemma shift_total (n k : ℕ) (u v : Bool) :
    count (n + k) u v = total n u v (iterate k u v) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [show n + (k + 1) = (n + 1) + k by omega, ih, total_step]
    rfl

set_option maxHeartbeats 4000000 in
lemma iter_vec_rec : ∀ u v : Bool,
    let v1 := iterVec 1 u v
    let v2 := iterVec 2 u v
    let v3 := iterVec 3 u v
    let v4 := iterVec 4 u v
    ∀ q : Fin 47, v4.getD q.val 0 = 7 * v3.getD q.val 0 - 14 * v2.getD q.val 0 + 8 * v1.getD q.val 0 := by
  decide +kernel

lemma iter_rec (u v : Bool) (q : Fin 47) :
    iterate 4 u v q.val = 7 * iterate 3 u v q.val - 14 * iterate 2 u v q.val + 8 * iterate 1 u v q.val := by
  simpa only [iterVec_eq _ u v q.val q.isLt] using iter_vec_rec u v q

lemma count_rec (n : ℕ) (u v : Bool) :
    count (n + 4) u v = 7 * count (n + 3) u v - 14 * count (n + 2) u v + 8 * count (n + 1) u v := by
  simp only [shift_total, total, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro x _
  exact iter_rec u v ⟨_, small_address n _ x y⟩

lemma reflect_square (t : ℕ) (f : ℕ → ℕ → ℤ) :
    ∑ j ∈ Finset.range (2 * t + 1), ∑ i ∈ Finset.range (2 * t + 1),
      f (((i : ℤ) - ↑t).natAbs) (((j : ℤ) - ↑t).natAbs) =
    4 * (∑ j ∈ Finset.range (t + 1), ∑ i ∈ Finset.range (t + 1), f i j) -
      2 * (∑ j ∈ Finset.range (t + 1), f 0 j) - 2 * (∑ i ∈ Finset.range (t + 1), f i 0) + f 0 0 := by
  rw [reflect_sum t (fun y => ∑ i ∈ Finset.range (2 * t + 1), f (((i : ℤ) - ↑t).natAbs) y)]
  have inner (y : ℕ) := reflect_sum t (fun i => f i y)
  simp only [inner]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma count_eq (n : ℕ) (u v : Bool) :
    count n u v = ∑ j ∈ Finset.range (span v n), ∑ i ∈ Finset.range (span u n),
      ((value (2 ^ n - 1) i j).toNat : ℤ) := by
  have hpos : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  unfold count total weight
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro i hi
  simp only [Finset.mem_range] at hi hj
  have hb (b : Bool) : span b n ≤ 2 ^ n := by cases b <;> simp [span, Nat.one_le_two_pow]
  rw [at_width n _ _ _ (by omega) (lt_of_lt_of_le hi (hb u)) (lt_of_lt_of_le hj (hb v))]

lemma count_eq_iterVec (k : ℕ) (u v : Bool) :
    count k u v = (iterVec k u v).getD 0 0 := by
  have h := shift_total 0 k u v
  rw [Nat.zero_add] at h
  rw [h]
  have su : span u 0 = 1 := by cases u <;> rfl
  have sv : span v 0 = 1 := by cases v <;> rfl
  unfold total
  rw [su, sv]
  simp only [Finset.sum_range_one, address]
  exact (iterVec_eq k u v 0 (by decide)).symm

lemma sampled_eq (n r : ℕ) (hr : r = 131) : (countOn r (2 ^ n - 1) : ℤ) =
    4 * count n true true - 2 * count n false true - 2 * count n true false + count n false false := by
  have h : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  unfold countOn
  rw [stages r _ hr]
  dsimp only
  rw [sum_gridRows]
  unfold plane
  rw [reflect_square (2 ^ n - 1) (fun i j => ((value (2 ^ n - 1) i j).toNat : ℤ))]
  simp only [count_eq, span, ↓reduceIte, Bool.false_eq_true, Finset.sum_range_one,
    show (2 : ℕ) ^ n - 1 + 1 = 2 ^ n by omega]

lemma sampled_fast (n r : ℕ) (hr : r = 131) : (countOn r (2 ^ n - 1) : ℤ) =
    4 * (iterVec n true true).getD 0 0 - 2 * (iterVec n false true).getD 0 0 -
      2 * (iterVec n true false).getD 0 0 + (iterVec n false false).getD 0 0 := by
  rw [sampled_eq n r hr]
  simp only [count_eq_iterVec]

end Scale131


section Proof_a273676

lemma a_rec833 (n : ℕ) : (a (n + 5) : ℤ) = 7 * a (n + 4) - 14 * a (n + 3) + 8 * a (n + 2) := by
  simp only [a, Scale833.sampled_eq _ 833 (Or.inl rfl), Scale833.count_rec n]
  ring

lemma a_init833 : (a 2 : ℤ) = 33 ∧ (a 3 : ℤ) = 161 ∧ (a 4 : ℤ) = 705 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [a, Scale833.sampled_fast 2 833 (Or.inl rfl)]; decide +kernel
  · rw [a, Scale833.sampled_fast 3 833 (Or.inl rfl)]; decide +kernel
  · rw [a, Scale833.sampled_fast 4 833 (Or.inl rfl)]; decide +kernel

lemma closed_a_aux (F : ℕ → ℤ)
    (v2 : F 2 = 33) (v3 : F 3 = 161) (v4 : F 4 = 705)
    (hrec : ∀ k, F (k + 5) = 7 * F (k + 4) - 14 * F (k + 3) + 8 * F (k + 2))
    (n : ℕ) (hn : 1 < n) : F n = 3 * 4 ^ n - 4 * 2 ^ n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < 5
    · interval_cases n <;> norm_num [v2, v3, v4]
    · let k := n - 5
      have hk : n = k + 5 := by dsimp [k]; omega
      have h1 := ih (k + 2) (by omega) (by omega)
      have h2 := ih (k + 3) (by omega) (by omega)
      have h3 := ih (k + 4) (by omega) (by omega)
      rw [hk, hrec k, h1, h2, h3]
      simp only [pow_add]
      ring

lemma closed_a (n : ℕ) (hn : 1 < n) : (a n : ℤ) = 3 * 4 ^ n - 4 * 2 ^ n + 1 :=
  closed_a_aux (fun m => (a m : ℤ)) a_init833.1 a_init833.2.1 a_init833.2.2 a_rec833 n hn

lemma a_rec131 (n : ℕ) :
    (a270222 (n + 4) : ℤ) = 7 * a270222 (n + 3) - 14 * a270222 (n + 2) + 8 * a270222 (n + 1) := by
  simp only [a270222, Scale131.sampled_eq _ 131 rfl, Scale131.count_rec n]
  ring

lemma a_init131 : (a270222 2 : ℤ) = 33 ∧ (a270222 3 : ℤ) = 161 ∧ (a270222 4 : ℤ) = 705 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [a270222, Scale131.sampled_fast 2 131 rfl]; decide +kernel
  · rw [a270222, Scale131.sampled_fast 3 131 rfl]; decide +kernel
  · rw [a270222, Scale131.sampled_fast 4 131 rfl]; decide +kernel

lemma closed_131_aux (F : ℕ → ℤ)
    (v2 : F 2 = 33) (v3 : F 3 = 161) (v4 : F 4 = 705)
    (hrec : ∀ k, F (k + 4) = 7 * F (k + 3) - 14 * F (k + 2) + 8 * F (k + 1))
    (n : ℕ) (hn : 1 < n) : F n = 3 * 4 ^ n - 4 * 2 ^ n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < 5
    · interval_cases n <;> norm_num [v2, v3, v4]
    · let k := n - 4
      have hk : n = k + 4 := by dsimp [k]; omega
      have h1 := ih (k + 1) (by omega) (by omega)
      have h2 := ih (k + 2) (by omega) (by omega)
      have h3 := ih (k + 3) (by omega) (by omega)
      rw [hk, hrec k, h1, h2, h3]
      simp only [pow_add]
      ring

lemma closed_131 (n : ℕ) (hn : 1 < n) : (a270222 n : ℤ) = 3 * 4 ^ n - 4 * 2 ^ n + 1 :=
  closed_131_aux (fun m => (a270222 m : ℤ)) a_init131.1 a_init131.2.1 a_init131.2.2 a_rec131 n hn

end Proof_a273676


lemma interval_range (t : ℕ) (f : ℤ → ℤ) :
    ∑ x ∈ Finset.Icc (-(t:ℤ)) t, f x =
      ∑ i ∈ Finset.range (2*t+1), f ((i:ℤ)-t) := by
  apply Finset.sum_bij' (fun (x : ℤ) _ => (x+t).toNat) (fun (i : ℕ) _ => (i:ℤ)-t)
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    apply Finset.mem_range.mpr
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    omega
  · intro i hi
    omega
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    congr 1
    omega

lemma count_sum (r t : ℕ) :
    (OMA.S_oeis_a273676.count r t : ℤ) = ∑ j ∈ Finset.range (2*t+1),
      ∑ i ∈ Finset.range (2*t+1),
        ((OMA.S_oeis_a273676.state r t ((i:ℤ)-t) ((j:ℤ)-t)).toNat : ℤ) := by
  unfold OMA.S_oeis_a273676.count
  rw [Finset.card_filter, Finset.sum_product_right]
  push_cast
  rw [interval_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [interval_range]
  apply Finset.sum_congr rfl
  intro i _
  cases OMA.S_oeis_a273676.state r t ((i:ℤ)-t) ((j:ℤ)-t) <;> simp

lemma state_plane833 (r t : ℕ) (hr : r = 833 ∨ r = 849) (x y : ℤ) :
    OMA.S_oeis_a273676.state r t x y = Scale833.plane t x y := by
  induction t generalizing x y with
  | zero => rw [Scale833.plane_zero]; rfl
  | succ t ih =>
    rw [Scale833.plane_step r t x y hr]
    simp only [OMA.S_oeis_a273676.state, Scale833.localRule, ih]

lemma count_eq833 (r t : ℕ) (hr : r = 833 ∨ r = 849) :
    OMA.S_oeis_a273676.count r t = countOn r t := by
  apply Int.ofNat.inj
  change (OMA.S_oeis_a273676.count r t : ℤ) = (countOn r t : ℤ)
  unfold countOn
  rw [Scale833.stages r t hr]
  rw [count_sum, Scale833.sum_gridRows]
  simp only [state_plane833 r t hr]

lemma state_plane131 (r t : ℕ) (hr : r = 131) (x y : ℤ) :
    OMA.S_oeis_a273676.state r t x y = Scale131.plane t x y := by
  induction t generalizing x y with
  | zero => rw [Scale131.plane_zero]; rfl
  | succ t ih =>
    rw [Scale131.plane_step r t x y hr]
    simp only [OMA.S_oeis_a273676.state, Scale131.localRule, ih]

lemma count_eq131 (r t : ℕ) (hr : r = 131) :
    OMA.S_oeis_a273676.count r t = countOn r t := by
  apply Int.ofNat.inj
  change (OMA.S_oeis_a273676.count r t : ℤ) = (countOn r t : ℤ)
  unfold countOn
  rw [Scale131.stages r t hr]
  rw [count_sum, Scale131.sum_gridRows]
  simp only [state_plane131 r t hr]

lemma series : PowerSeries.mk (fun n => (a n : ℤ)) *
    ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
    1 - 3 * PowerSeries.X + 19 * PowerSeries.X ^ 2 - 22 * PowerSeries.X ^ 3 +
      8 * PowerSeries.X ^ 4 := by
  let F : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  let X : PowerSeries ℤ := PowerSeries.X
  change F * ((1-X)*(1-2*X)*(1-4*X)) = _
  have h : F * ((1-X)*(1-2*X)*(1-4*X)) =
      F - (7:ℤ) • (F*X^1) + (14:ℤ) • (F*X^2) - (8:ℤ) • (F*X^3) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have p : (1 - 3*X + 19*X^2 - 22*X^3 + 8*X^4 : PowerSeries ℤ) =
      X^0 - (3:ℤ) • X^1 + (19:ℤ) • X^2 - (22:ℤ) • X^3 + (8:ℤ) • X^4 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [h, p]
  ext n
  simp only [X, map_add, map_sub, map_zsmul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_X_pow, F, PowerSeries.coeff_mk]
  simp only [zsmul_eq_mul]
  by_cases hn : n < 5
  · have h0 : (a 0 : ℤ) = 1 := by decide
    have h1 : (a 1 : ℤ) = 4 := by decide
    rcases a_init833 with ⟨h2,h3,h4⟩
    generalize a = g at h0 h1 h2 h3 h4 ⊢
    interval_cases n <;> norm_num [h0,h1,h2,h3,h4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m+5 := ⟨n-5, by omega⟩
    simp
    linarith [a_rec833 m]

end Adapt273676

theorem OMA.solution : type_of% @OMA.S_oeis_a273676.main := by
  unfold OMA.S_oeis_a273676.a
  simp only [Adapt273676.count_eq833 833 _ (Or.inl rfl),
    Adapt273676.count_eq833 849 _ (Or.inr rfl), Adapt273676.count_eq131 131 _ rfl]
  refine ⟨?_, ?_, Adapt273676.closed_a, ?_, Adapt273676.series⟩
  · intro n
    apply Int.ofNat.inj
    exact (Adapt273676.Scale833.sampled_eq n 849 (Or.inr rfl)).trans
      (Adapt273676.Scale833.sampled_eq n 833 (Or.inl rfl)).symm
  · intro n hn
    apply Int.ofNat.inj
    exact (Adapt273676.closed_a n hn).trans (Adapt273676.closed_131 n hn).symm
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m+5 := ⟨n-5, by omega⟩
    exact_mod_cast Adapt273676.a_rec833 m
