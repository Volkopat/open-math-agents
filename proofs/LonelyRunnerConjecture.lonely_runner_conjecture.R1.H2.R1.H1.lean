import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1_H2_R1
import Mathlib

-- Step LonelyRunnerConjecture.lonely_runner_conjecture.R1.H2.R1.H1: hypothesis H1 of reduction LonelyRunnerConjecture.lonely_runner_conjecture.R1.H2.R1
-- Credit: @Pampasgras
-- H1 := ∀ (w : Fin 5 → ℕ),     (∀ i : Fin 5, 0 < w i) →     StrictMono w →     Finset.univ.gcd w = 1 →     (∀ i₀ : Fin 5, (Finset.univ.erase i₀).gcd w = 1) →     (∀ j : ℕ, 2 ≤ j → j ≤ 6 → ∃ i : Fin 5, j ∣ w i) →     (∀ q : ℕ, Nat.Prime q → 3 ≤ q → (Finset.univ.filter (fun i : Fin 5 => q ∣ w i)).card ≤ 2) →     (∃ i j : Fin 5, i.val + 1 = j.val ∧ j.val + 1 < 5 ∧ (5 - 1) * w j < 2 * 5 * w i) →     (∑ S ∈ (Finset.univ : Finset (Fin 5)).powerset.erase ∅, S.gcd w) ≤ (Nat.choose 6 2) ^ 4 →     ∃ t : ℝ, t ≥ 0 ∧       ∀ i : Fin 5, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((5 + 1 : ℕ) : ℝ)  -- Bounded, prime-filtered 7-runner integer regime (k = 6, with 1 or 2 multiples of 7).

-- Six lonely runners (k = 5) on the bounded regime of H1.
-- Method: Rosenfeld (arXiv 2509.14111, Lemma 6 and Table 1) with the sieve of Trakulthongchai
-- (arXiv 2511.22427, Lemma 7). For each prime p in 29..71, a speed tuple with no speed divisible by p
-- has a lonely time s/p, s/(2p) or s/(6p): this is a finite check on residues, done by the kernel
-- on bitmask tables. So a counterexample has 60*29*31*...*71 dividing the product of its speeds,
-- which contradicts the bound sum(w) <= 15^4 by AM-GM.

namespace LRC

/-- `x mod N` lies in `[N/6, 5N/6]`. -/
def g (N x : ℕ) : Bool := Nat.ble N (6 * (x % N)) && Nat.ble (6 * (x % N)) (5 * N)

/-- Evaluate `x` before continuing (keeps the kernel computation shared). -/
def force {α : Type} (x : ℕ) (f : ℕ → α) : α :=
  match x with
  | 0 => f 0
  | m + 1 => f (m + 1)

theorem force_eq {α : Type} (x : ℕ) (f : ℕ → α) : force x f = f x := by
  cases x <;> rfl

/-- Bitmask of `{j < n | f j}`. -/
def mk (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => mk f n ||| (bif f n then 2 ^ n else 0)

theorem mk_spec (f : ℕ → Bool) (n s : ℕ) (h : (mk f n).testBit s = true) : s < n ∧ f s = true := by
  induction n with
  | zero => simp [mk] at h
  | succ n ih =>
    rw [mk, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨Nat.lt_succ_of_lt (ih h).1, (ih h).2⟩
    · cases hf : f n with
      | false => simp [hf] at h
      | true =>
        simp only [hf, cond_true, Nat.testBit_two_pow, decide_eq_true_eq] at h
        subst h
        exact ⟨Nat.lt_succ_self _, hf⟩

/-- Table with one `W`-bit row per residue `r < n`: bit `s` of row `r` says `g N (s * r)`. -/
def tbl (N W : ℕ) (need : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc =>
    force (bif need n then acc ||| (mk (fun s => g N (s * n)) W <<< (W * n)) else acc)
      (tbl N W need n)

def row (T W r : ℕ) : ℕ := (T >>> (W * r)) % 2 ^ W

def Inv (N W T : ℕ) : Prop := ∀ i, T.testBit i = true → g N ((i % W) * (i / W)) = true

theorem inv_zero (N W : ℕ) : Inv N W 0 := by
  intro i hi
  simp at hi

theorem tbl_inv (N W : ℕ) (need : ℕ → Bool) (hW : 0 < W) (n acc : ℕ) (h : Inv N W acc) :
    Inv N W (tbl N W need n acc) := by
  induction n generalizing acc with
  | zero => simpa [tbl] using h
  | succ n ih =>
    rw [tbl, force_eq]
    apply ih
    cases need n with
    | false => simpa using h
    | true =>
      intro i hi
      simp only [cond_true, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftLeft,
        Bool.and_eq_true, decide_eq_true_eq] at hi
      rcases hi with hi | ⟨hge, hi⟩
      · exact h i hi
      · obtain ⟨hlt, hg⟩ := mk_spec _ _ _ hi
        obtain ⟨s, rfl⟩ : ∃ s, i = W * n + s := ⟨i - W * n, by omega⟩
        rw [Nat.add_sub_cancel_left] at hlt hg
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt, Nat.mul_add_div hW, Nat.div_eq_of_lt hlt,
          Nat.add_zero]
        exact hg

theorem row_spec {N W T : ℕ} (hT : Inv N W T) (hW : 0 < W) {r s : ℕ}
    (h : (row T W r).testBit s = true) : g N (s * r) = true := by
  rw [row, Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_shiftRight] at h
  have := hT _ h.2
  rwa [Nat.mul_add_mod, Nat.mod_eq_of_lt h.1, Nat.mul_add_div hW, Nat.div_eq_of_lt h.1,
    Nat.add_zero] at this

def G (N s a b c d e : ℕ) : Prop :=
  g N (s * a) = true ∧ g N (s * b) = true ∧ g N (s * c) = true ∧ g N (s * d) = true ∧
    g N (s * e) = true

theorem leaf {N W T : ℕ} (hT : Inv N W T) (hW : 0 < W) {a b c d e : ℕ}
    (h : Nat.ble 1 (row T W a &&& row T W b &&& row T W c &&& row T W d &&& row T W e) = true) :
    ∃ s, G N s a b c d e := by
  have hne : row T W a &&& row T W b &&& row T W c &&& row T W d &&& row T W e ≠ 0 := by
    have := Nat.le_of_ble_eq_true h
    omega
  obtain ⟨s, hs⟩ := Nat.exists_testBit_of_ne_zero hne
  simp only [Nat.testBit_and, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩ := hs
  exact ⟨s, row_spec hT hW ha, row_spec hT hW hb, row_spec hT hW hc, row_spec hT hW hd,
    row_spec hT hW he⟩

def allB : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f n && allB n f

theorem allB_spec {n : ℕ} {f : ℕ → Bool} (h : allB n f = true) (x : ℕ) (hx : x < n) :
    f x = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [allB, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hx with h1 | h1
    · exact ih h.2 h1
    · rw [h1]
      exact h.1

def allGe : ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, _, _ => true
  | n + 1, lo, f => Nat.blt n lo || (f n && allGe n lo f)

theorem allGe_spec {n lo : ℕ} {f : ℕ → Bool} (h : allGe n lo f = true) (x : ℕ) (hlo : lo ≤ x)
    (hx : x < n) : f x = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [allGe, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | h
    · rw [Nat.blt_eq] at h
      omega
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hx with h1 | h1
      · exact ih h.2 h1
      · rw [h1]
        exact h.1

def c2 (a b c d e : ℕ) : Bool := Nat.ble 2 (a % 2 + b % 2 + c % 2 + d % 2 + e % 2)

def c3 (a b c d e : ℕ) : Bool :=
  Nat.ble 2 ((a % 3 + 1) / 2 + (b % 3 + 1) / 2 + (c % 3 + 1) / 2 + (d % 3 + 1) / 2 + (e % 3 + 1) / 2)

def lift6 (p W T a b c d e : ℕ) : Bool :=
  allB 3 fun i => force (row T W (a + 2 * (p * i))) fun m0 =>
  allB 3 fun j => force (m0 &&& row T W (b + 2 * (p * j))) fun m1 =>
  allB 3 fun k => force (m1 &&& row T W (c + 2 * (p * k))) fun m2 =>
  allB 3 fun l => force (m2 &&& row T W (d + 2 * (p * l))) fun m3 =>
  allB 3 fun m => Nat.ble 1 (m3 &&& row T W (e + 2 * (p * m)))
    || !(c3 (a + 2 * (p * i)) (b + 2 * (p * j)) (c + 2 * (p * k)) (d + 2 * (p * l)) (e + 2 * (p * m)))

def lift2 (p W2 T2 W6 T6 a b c d e : ℕ) : Bool :=
  allB 2 fun i => force (row T2 W2 (a + p * i)) fun m0 =>
  allB 2 fun j => force (m0 &&& row T2 W2 (b + p * j)) fun m1 =>
  allB 2 fun k => force (m1 &&& row T2 W2 (c + p * k)) fun m2 =>
  allB 2 fun l => force (m2 &&& row T2 W2 (d + p * l)) fun m3 =>
  allB 2 fun m => Nat.ble 1 (m3 &&& row T2 W2 (e + p * m))
    || !(c2 (a + p * i) (b + p * j) (c + p * k) (d + p * l) (e + p * m))
    || lift6 p W6 T6 (a + p * i) (b + p * j) (c + p * k) (d + p * l) (e + p * m)

def chk (p h : ℕ) : Bool :=
  force (tbl p (h + 1) (fun _ => true) (h + 1) 0) fun T1 =>
  force (tbl (2 * p) (p + 1) (fun _ => true) (2 * p) 0) fun T2 =>
  force (tbl (6 * p) (3 * p + 1) (fun r => Nat.ble (r % p) h) (6 * p) 0) fun T6 =>
  force (row T1 (h + 1) 1) fun m0 =>
  allGe (h + 1) 1 fun a1 => force (m0 &&& row T1 (h + 1) a1) fun m1 =>
  allGe (h + 1) a1 fun a2 => force (m1 &&& row T1 (h + 1) a2) fun m2 =>
  allGe (h + 1) a2 fun a3 => force (m2 &&& row T1 (h + 1) a3) fun m3 =>
  allGe (h + 1) a3 fun a4 => Nat.ble 1 (m3 &&& row T1 (h + 1) a4)
    || lift2 p (p + 1) T2 (3 * p + 1) T6 1 a1 a2 a3 a4

theorem lift6_sound {p W T a b c d e : ℕ} (hT : Inv (6 * p) W T) (hW : 0 < W)
    (h : lift6 p W T a b c d e = true) (i j k l m : ℕ) (hi : i < 3) (hj : j < 3) (hk : k < 3)
    (hl : l < 3) (hm : m < 3)
    (hc : c3 (a + 2 * (p * i)) (b + 2 * (p * j)) (c + 2 * (p * k)) (d + 2 * (p * l))
      (e + 2 * (p * m)) = true) :
    ∃ s, G (6 * p) s (a + 2 * (p * i)) (b + 2 * (p * j)) (c + 2 * (p * k)) (d + 2 * (p * l))
      (e + 2 * (p * m)) := by
  simp only [lift6, force_eq] at h
  have h1 := allB_spec (allB_spec (allB_spec (allB_spec (allB_spec h i hi) j hj) k hk) l hl) m hm
  simp only [hc, Bool.not_true, Bool.or_false] at h1
  exact leaf hT hW h1

theorem lift2_sound {p W2 T2 W6 T6 a b c d e : ℕ} (h2 : Inv (2 * p) W2 T2) (hW2 : 0 < W2)
    (h : lift2 p W2 T2 W6 T6 a b c d e = true) (i j k l m : ℕ) (hi : i < 2) (hj : j < 2)
    (hk : k < 2) (hl : l < 2) (hm : m < 2)
    (hc : c2 (a + p * i) (b + p * j) (c + p * k) (d + p * l) (e + p * m) = true) :
    (∃ s, G (2 * p) s (a + p * i) (b + p * j) (c + p * k) (d + p * l) (e + p * m)) ∨
      lift6 p W6 T6 (a + p * i) (b + p * j) (c + p * k) (d + p * l) (e + p * m) = true := by
  simp only [lift2, force_eq] at h
  have h1 := allB_spec (allB_spec (allB_spec (allB_spec (allB_spec h i hi) j hj) k hk) l hl) m hm
  simp only [hc, Bool.not_true, Bool.or_false, Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact Or.inl (leaf h2 hW2 h1)
  · exact Or.inr h1

theorem chk_all {p h : ℕ} (hc : chk p h = true) (hp : 0 < p) (a1 a2 a3 a4 : ℕ) (h1 : 1 ≤ a1)
    (h12 : a1 ≤ a2) (h23 : a2 ≤ a3) (h34 : a3 ≤ a4) (h4 : a4 ≤ h)
    (e0 e1 e2 e3 e4 : ℕ) (he0 : e0 < 2) (he1 : e1 < 2) (he2 : e2 < 2) (he3 : e3 < 2) (he4 : e4 < 2)
    (c0 c1 c2' c3' c4 : ℕ) (hc0 : c0 < 3) (hc1 : c1 < 3) (hc2 : c2' < 3) (hc3 : c3' < 3)
    (hc4 : c4 < 3)
    (hpar : c2 (1 + p * e0) (a1 + p * e1) (a2 + p * e2) (a3 + p * e3) (a4 + p * e4) = true)
    (htri : c3 (1 + p * e0 + 2 * (p * c0)) (a1 + p * e1 + 2 * (p * c1)) (a2 + p * e2 + 2 * (p * c2'))
      (a3 + p * e3 + 2 * (p * c3')) (a4 + p * e4 + 2 * (p * c4)) = true) :
    (∃ s, G p s 1 a1 a2 a3 a4) ∨
    (∃ s, G (2 * p) s (1 + p * e0) (a1 + p * e1) (a2 + p * e2) (a3 + p * e3) (a4 + p * e4)) ∨
    (∃ s, G (6 * p) s (1 + p * e0 + 2 * (p * c0)) (a1 + p * e1 + 2 * (p * c1))
      (a2 + p * e2 + 2 * (p * c2')) (a3 + p * e3 + 2 * (p * c3')) (a4 + p * e4 + 2 * (p * c4))) := by
  simp only [chk, force_eq] at hc
  have h5 := allGe_spec (allGe_spec (allGe_spec (allGe_spec hc a1 h1 (by omega)) a2 h12 (by omega))
    a3 h23 (by omega)) a4 h34 (by omega)
  rw [Bool.or_eq_true] at h5
  rcases h5 with h5 | h5
  · exact Or.inl (leaf (tbl_inv _ _ _ (by omega) _ _ (inv_zero _ _)) (by omega) h5)
  · rcases lift2_sound (tbl_inv _ _ _ (by omega) _ _ (inv_zero _ _)) (by omega) h5 e0 e1 e2 e3 e4
      he0 he1 he2 he3 he4 hpar with h6 | h6
    · exact Or.inr (Or.inl h6)
    · exact Or.inr (Or.inr (lift6_sound (tbl_inv _ _ _ (by omega) _ _ (inv_zero _ _)) (by omega) h6
        c0 c1 c2' c3' c4 hc0 hc1 hc2 hc3 hc4 htri))

/-- The runner with speed `z` is at distance at least `1/6` from the origin at time `t`. -/
def far (t : ℝ) (z : ℤ) : Prop := (1 : ℝ) / 6 ≤ dist ((t * (z : ℝ) : ℝ) : UnitAddCircle) 0

theorem dist_ge (x : ℝ) (n : ℤ) (f : ℝ) (hx : x = n + f) (h1 : 1 / 6 ≤ f) (h2 : f ≤ 5 / 6) :
    (1 : ℝ) / 6 ≤ dist (x : UnitAddCircle) 0 := by
  rw [dist_zero_right, UnitAddCircle.norm_eq, hx]
  generalize round ((n : ℝ) + f) = m
  rcases le_or_gt (m - n) 0 with h | h
  · have h' : ((m : ℝ) - n) ≤ 0 := by exact_mod_cast h
    rw [le_abs]
    left
    linarith
  · have h0 : (1 : ℤ) ≤ m - n := h
    have h' : (1 : ℝ) ≤ (m : ℝ) - n := by exact_mod_cast h0
    rw [le_abs]
    right
    linarith

theorem far_of_g {N s r : ℕ} {z k : ℤ} (hN : 0 < N) (hz : z = (r : ℤ) + (N : ℤ) * k)
    (hg : g N (s * r) = true) : far ((s : ℝ) / N) z := by
  rw [g, Bool.and_eq_true] at hg
  have h1 : N ≤ 6 * (s * r % N) := Nat.le_of_ble_eq_true hg.1
  have h2 : 6 * (s * r % N) ≤ 5 * N := Nat.le_of_ble_eq_true hg.2
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hdm : ((s : ℝ) * r) = (N : ℝ) * ((s * r / N : ℕ) : ℝ) + ((s * r % N : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod (s * r) N).symm
  have h1' : (N : ℝ) ≤ 6 * ((s * r % N : ℕ) : ℝ) := by exact_mod_cast h1
  have h2' : 6 * ((s * r % N : ℕ) : ℝ) ≤ 5 * (N : ℝ) := by exact_mod_cast h2
  unfold far
  refine dist_ge _ (((s * r / N : ℕ) : ℤ) + s * k) (((s * r % N : ℕ) : ℝ) / N) ?_ ?_ ?_
  · rw [hz]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    field_simp
    linear_combination hdm
  · rw [le_div_iff₀ hN']
    linarith
  · rw [div_le_iff₀ hN']
    linarith

theorem decomp (p : ℕ) (hp : 0 < p) (y : ℤ) :
    ∃ (a e c : ℕ) (k1 k2 k3 : ℤ), (a : ℤ) = y % p ∧ e < 2 ∧ c < 3 ∧
      y = (a : ℤ) + (p : ℤ) * k1 ∧
      y = ((a + p * e : ℕ) : ℤ) + 2 * ((p : ℤ) * k2) ∧
      y = ((a + p * e + 2 * (p * c) : ℕ) : ℤ) + 6 * ((p : ℤ) * k3) := by
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hy : y = y % p + p * (y / p) := (Int.emod_add_mul_ediv y p).symm
  have hm2 : y / p = y / p % 2 + 2 * (y / p / 2) := (Int.emod_add_mul_ediv _ 2).symm
  have hm3 : y / p / 2 = y / p / 2 % 3 + 3 * (y / p / 2 / 3) := (Int.emod_add_mul_ediv _ 3).symm
  have ha : ((y % p).toNat : ℤ) = y % p := Int.toNat_of_nonneg (Int.emod_nonneg _ hp')
  have he : ((y / p % 2).toNat : ℤ) = y / p % 2 := Int.toNat_of_nonneg (by omega)
  have hc : ((y / p / 2 % 3).toNat : ℤ) = y / p / 2 % 3 := Int.toNat_of_nonneg (by omega)
  refine ⟨(y % p).toNat, (y / p % 2).toNat, (y / p / 2 % 3).toNat, y / p, y / p / 2, y / p / 2 / 3,
    ha, by omega, by omega, ?_, ?_, ?_⟩
  · rw [ha]
    exact hy
  · push_cast
    rw [ha, he]
    linear_combination hy + (p : ℤ) * hm2
  · push_cast
    rw [ha, he, hc]
    linear_combination hy + (p : ℤ) * hm2 + 2 * (p : ℤ) * hm3

theorem core {p h : ℕ} (hc : chk p h = true) (hp : 0 < p) (y0 y1 y2 y3 y4 : ℤ)
    (h0 : y0 % p = 1) (h1 : 1 ≤ y1 % p) (h12 : y1 % p ≤ y2 % p) (h23 : y2 % p ≤ y3 % p)
    (h34 : y3 % p ≤ y4 % p) (h4 : y4 % p ≤ h)
    (hE : 2 ≤ y0 % 2 + y1 % 2 + y2 % 2 + y3 % 2 + y4 % 2)
    (hT : 2 ≤ (y0 % 3 + 1) / 2 + (y1 % 3 + 1) / 2 + (y2 % 3 + 1) / 2 + (y3 % 3 + 1) / 2
      + (y4 % 3 + 1) / 2) :
    ∃ t : ℝ, 0 ≤ t ∧ far t y0 ∧ far t y1 ∧ far t y2 ∧ far t y3 ∧ far t y4 := by
  obtain ⟨a0, e0, c0, k0, l0, n0, ha0, he0, hc0, hA0, hB0, hC0⟩ := decomp p hp y0
  obtain ⟨a1, e1, c1, k1, l1, n1, ha1, he1, hc1, hA1, hB1, hC1⟩ := decomp p hp y1
  obtain ⟨a2, e2, c2', k2, l2, n2, ha2, he2, hc2, hA2, hB2, hC2⟩ := decomp p hp y2
  obtain ⟨a3, e3, c3', k3, l3, n3, ha3, he3, hc3, hA3, hB3, hC3⟩ := decomp p hp y3
  obtain ⟨a4, e4, c4, k4, l4, n4, ha4, he4, hc4, hA4, hB4, hC4⟩ := decomp p hp y4
  have ha0' : a0 = 1 := by omega
  subst ha0'
  have hpar : c2 (1 + p * e0) (a1 + p * e1) (a2 + p * e2) (a3 + p * e3) (a4 + p * e4) = true := by
    apply Nat.ble_eq_true_of_le
    omega
  have htri : c3 (1 + p * e0 + 2 * (p * c0)) (a1 + p * e1 + 2 * (p * c1))
      (a2 + p * e2 + 2 * (p * c2')) (a3 + p * e3 + 2 * (p * c3')) (a4 + p * e4 + 2 * (p * c4))
      = true := by
    apply Nat.ble_eq_true_of_le
    omega
  have hp2 : 0 < 2 * p := by omega
  have hp6 : 0 < 6 * p := by omega
  rcases chk_all hc hp a1 a2 a3 a4 (by omega) (by omega) (by omega) (by omega) (by omega)
      e0 e1 e2 e3 e4 he0 he1 he2 he3 he4 c0 c1 c2' c3' c4 hc0 hc1 hc2 hc3 hc4 hpar htri with
    ⟨s, g0, g1, g2, g3, g4⟩ | ⟨s, g0, g1, g2, g3, g4⟩ | ⟨s, g0, g1, g2, g3, g4⟩
  · exact ⟨(s : ℝ) / p, by positivity, far_of_g hp hA0 g0, far_of_g hp hA1 g1, far_of_g hp hA2 g2,
      far_of_g hp hA3 g3, far_of_g hp hA4 g4⟩
  · exact ⟨(s : ℝ) / (2 * p : ℕ), by positivity,
      far_of_g (k := l0) hp2 (by rw [hB0]; push_cast; ring) g0, far_of_g (k := l1) hp2 (by rw [hB1]; push_cast; ring) g1,
      far_of_g (k := l2) hp2 (by rw [hB2]; push_cast; ring) g2, far_of_g (k := l3) hp2 (by rw [hB3]; push_cast; ring) g3,
      far_of_g (k := l4) hp2 (by rw [hB4]; push_cast; ring) g4⟩
  · exact ⟨(s : ℝ) / (6 * p : ℕ), by positivity,
      far_of_g (k := n0) hp6 (by rw [hC0]; push_cast; ring) g0, far_of_g (k := n1) hp6 (by rw [hC1]; push_cast; ring) g1,
      far_of_g (k := n2) hp6 (by rw [hC2]; push_cast; ring) g2, far_of_g (k := n3) hp6 (by rw [hC3]; push_cast; ring) g3,
      far_of_g (k := n4) hp6 (by rw [hC4]; push_cast; ring) g4⟩

theorem prime_case {p h : ℕ} (hc : chk p h = true) (hp : p.Prime) (hh : p = 2 * h + 1) (h5 : 5 ≤ p)
    (w : Fin 5 → ℕ) (hE : 2 ≤ ∑ i, (w i : ℤ) % 2) (hT : 2 ≤ ∑ i, ((w i : ℤ) % 3 + 1) / 2)
    (hnd : ∀ i, ¬ p ∣ w i) : ∃ t : ℝ, 0 ≤ t ∧ ∀ i, far t (w i) := by
  have hp0 : 0 < p := hp.pos
  have hco6 : Nat.Coprime 6 p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases p <;> omega
  have hcow : Nat.Coprime (w 0) p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (hnd 0))
  obtain ⟨v, -, hv⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcow hp.one_lt
  obtain ⟨u, hu6, hup⟩ := Nat.chineseRemainder hco6 1 v
  have hu6' : u % 6 = 1 := hu6
  have hu0 : u * w 0 % p = 1 := by
    have h1 := hup.mul_right (w 0)
    rw [Nat.ModEq] at h1
    rw [h1, Nat.mul_comm]
    exact hv
  have hpu : ¬ p ∣ u := by
    intro hd
    have h1 : p ∣ u * w 0 := Dvd.dvd.mul_right hd _
    rw [Nat.dvd_iff_mod_eq_zero] at h1
    omega
  have hpuw : ∀ i, ¬ p ∣ u * w i := fun i hd => (hp.dvd_mul.1 hd).elim hpu (hnd i)
  obtain ⟨u', hu'⟩ : ∃ u', u = 6 * u' + 1 := ⟨u / 6, by omega⟩
  let z : Fin 5 → ℤ := fun i =>
    if u * w i % p ≤ h then ((u * w i : ℕ) : ℤ) else -((u * w i : ℕ) : ℤ)
  have hz : ∀ i, 1 ≤ z i % p ∧ z i % p ≤ h ∧ z i % 2 = (w i : ℤ) % 2 ∧
      (z i % 3 + 1) / 2 = ((w i : ℤ) % 3 + 1) / 2 ∧ ∀ t : ℝ, far t (z i) → far (t * u) (w i) := by
    intro i
    have hr0 : u * w i % p ≠ 0 := fun h0 => hpuw i (Nat.dvd_of_mod_eq_zero h0)
    have hrlt : u * w i % p < p := Nat.mod_lt _ hp0
    have hx : u * w i = 6 * (u' * w i) + w i := by
      rw [hu']
      ring
    have hdm : ((u * w i : ℕ) : ℤ) = (p : ℤ) * ((u * w i / p : ℕ) : ℤ) + ((u * w i % p : ℕ) : ℤ) := by
      exact_mod_cast (Nat.div_add_mod (u * w i) p).symm
    obtain ⟨r, hr⟩ : ∃ r, r = u * w i % p := ⟨_, rfl⟩
    rw [← hr] at hr0 hrlt hdm
    by_cases hle : u * w i % p ≤ h
    · have hzi : z i = ((u * w i : ℕ) : ℤ) := if_pos hle
      rw [← hr] at hle
      have hmod : z i % p = (r : ℤ) := by
        rw [hzi, hdm, Int.add_comm, Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      intro t ht
      unfold far at ht ⊢
      have h1 : t * ((z i : ℤ) : ℝ) = t * u * (((w i : ℕ) : ℤ) : ℝ) := by
        rw [hzi]
        push_cast
        ring
      rwa [h1] at ht
    · have hzi : z i = -((u * w i : ℕ) : ℤ) := if_neg hle
      rw [← hr] at hle
      have hmod : z i % p = (p : ℤ) - (r : ℤ) := by
        have h1 : z i = ((p : ℤ) - (r : ℤ)) + (p : ℤ) * (-((u * w i / p : ℕ) : ℤ) - 1) := by
          rw [hzi, hdm]
          ring
        rw [h1, Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      have h3 : (z i % 3 + 1) / 2 = ((w i : ℤ) % 3 + 1) / 2 := by
        rcases (by omega : (w i : ℤ) % 3 = 0 ∨ (w i : ℤ) % 3 = 1 ∨ (w i : ℤ) % 3 = 2) with
          h3 | h3 | h3 <;> omega
      refine ⟨by omega, by omega, by omega, h3, ?_⟩
      intro t ht
      unfold far at ht ⊢
      have h1 : t * ((z i : ℤ) : ℝ) = -(t * u * (((w i : ℕ) : ℤ) : ℝ)) := by
        rw [hzi]
        push_cast
        ring
      rw [h1, AddCircle.coe_neg, dist_zero_right, norm_neg, ← dist_zero_right] at ht
      exact ht
  let σ := Tuple.sort (fun i => z i % (p : ℤ))
  have hmono : Monotone ((fun i => z i % (p : ℤ)) ∘ σ) := Tuple.monotone_sort _
  have hle0 : u * w 0 % p ≤ h := by omega
  have hz0 : z 0 % p = 1 := by
    have hzi : z 0 = ((u * w 0 : ℕ) : ℤ) := if_pos hle0
    rw [hzi, ← Int.natCast_mod, hu0]
    rfl
  have hy0 : z (σ 0) % p = 1 := by
    have h1 := (hz (σ 0)).1
    have h2 : z (σ 0) % p ≤ z (σ (σ.symm 0)) % p := hmono (Fin.zero_le _)
    rw [Equiv.apply_symm_apply, hz0] at h2
    omega
  have hE' : 2 ≤ z (σ 0) % 2 + z (σ 1) % 2 + z (σ 2) % 2 + z (σ 3) % 2 + z (σ 4) % 2 := by
    have h1 : ∑ i, z (σ i) % 2 = ∑ i, (w i : ℤ) % 2 := by
      rw [Equiv.sum_comp σ (fun i => z i % 2)]
      exact Finset.sum_congr rfl (fun i _ => (hz i).2.2.1)
    rw [Fin.sum_univ_five] at h1
    omega
  have hT' : 2 ≤ (z (σ 0) % 3 + 1) / 2 + (z (σ 1) % 3 + 1) / 2 + (z (σ 2) % 3 + 1) / 2
      + (z (σ 3) % 3 + 1) / 2 + (z (σ 4) % 3 + 1) / 2 := by
    have h1 : ∑ i, (z (σ i) % 3 + 1) / 2 = ∑ i, ((w i : ℤ) % 3 + 1) / 2 := by
      rw [Equiv.sum_comp σ (fun i => (z i % 3 + 1) / 2)]
      exact Finset.sum_congr rfl (fun i _ => (hz i).2.2.2.1)
    rw [Fin.sum_univ_five] at h1
    omega
  obtain ⟨t, ht, f0, f1, f2, f3, f4⟩ := core hc hp0 (z (σ 0)) (z (σ 1)) (z (σ 2)) (z (σ 3))
    (z (σ 4)) hy0 (hz _).1 (hmono (by decide : (1 : Fin 5) ≤ 2)) (hmono (by decide : (2 : Fin 5) ≤ 3))
    (hmono (by decide : (3 : Fin 5) ≤ 4)) (hz _).2.1 hE' hT'
  have hall : ∀ k : Fin 5, far t (z (σ k)) := by
    intro k
    fin_cases k <;> assumption
  refine ⟨t * u, by positivity, fun i => ?_⟩
  have h1 := hall (σ.symm i)
  rw [Equiv.apply_symm_apply] at h1
  exact (hz i).2.2.2.2 t h1

theorem amgm5 (x : Fin 5 → ℝ) (hx : ∀ i, 0 ≤ x i) : ∏ i, x i ≤ ((∑ i, x i) / 5) ^ 5 := by
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : Fin 5 => (1 : ℝ) / 5) x
    (fun _ _ => by norm_num) (by simp) (fun i _ => hx i)
  have h2 : ∑ i : Fin 5, (1 : ℝ) / 5 * x i = (∑ i, x i) / 5 := by
    rw [← Finset.mul_sum]
    ring
  rw [h2] at h
  have h3 : (∏ i, x i ^ ((1 : ℝ) / 5)) ^ 5 = ∏ i, x i := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hx i)]
    norm_num
  rw [← h3]
  exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hx i) _)) h 5

theorem chk29 : chk 29 14 = true := by decide +kernel

theorem chk31 : chk 31 15 = true := by decide +kernel

theorem chk37 : chk 37 18 = true := by decide +kernel

theorem chk41 : chk 41 20 = true := by decide +kernel

theorem chk43 : chk 43 21 = true := by decide +kernel

theorem chk47 : chk 47 23 = true := by decide +kernel

theorem chk53 : chk 53 26 = true := by decide +kernel

theorem chk59 : chk 59 29 = true := by decide +kernel

theorem chk61 : chk 61 30 = true := by decide +kernel

theorem chk67 : chk 67 33 = true := by decide +kernel

theorem chk71 : chk 71 35 = true := by decide +kernel

end LRC

theorem OMA.solution : OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1_H2_R1.H1 := by
  intro w hpos _ _ herase hsieve _ _ hsum
  have hunit : ∀ q : ℕ, 1 < q → ∃ i j : Fin 5, i ≠ j ∧ ¬ q ∣ w i ∧ ¬ q ∣ w j := by
    intro q hq
    have key : ∀ i₀ : Fin 5, ∃ j, j ≠ i₀ ∧ ¬ q ∣ w j := by
      intro i₀
      by_contra hcon
      push Not at hcon
      have h1 : q ∣ (Finset.univ.erase i₀).gcd w :=
        Finset.dvd_gcd (fun j hj => hcon j (Finset.ne_of_mem_erase hj))
      rw [herase i₀] at h1
      have := Nat.le_of_dvd one_pos h1
      omega
    obtain ⟨j, _, hj⟩ := key 0
    obtain ⟨k, hk, hk'⟩ := key j
    exact ⟨j, k, hk.symm, hj, hk'⟩
  have hE : 2 ≤ ∑ i, (w i : ℤ) % 2 := by
    obtain ⟨i, j, hij, hi, hj⟩ := hunit 2 (by norm_num)
    have h1 := Finset.add_le_sum (f := fun i => (w i : ℤ) % 2) (s := Finset.univ)
      (fun i _ => by omega) (Finset.mem_univ i) (Finset.mem_univ j) hij
    have h2 : (w i : ℤ) % 2 = 1 := by omega
    have h3 : (w j : ℤ) % 2 = 1 := by omega
    simp only [h2, h3] at h1
    omega
  have hT : 2 ≤ ∑ i, ((w i : ℤ) % 3 + 1) / 2 := by
    obtain ⟨i, j, hij, hi, hj⟩ := hunit 3 (by norm_num)
    have h1 := Finset.add_le_sum (f := fun i => ((w i : ℤ) % 3 + 1) / 2) (s := Finset.univ)
      (fun i _ => by omega) (Finset.mem_univ i) (Finset.mem_univ j) hij
    have h2 : ((w i : ℤ) % 3 + 1) / 2 = 1 := by omega
    have h3 : ((w j : ℤ) % 3 + 1) / 2 = 1 := by omega
    simp only [h2, h3] at h1
    omega
  by_contra hcon
  have key : ∀ p h : ℕ, LRC.chk p h = true → p.Prime → p = 2 * h + 1 → 5 ≤ p → ∃ i, p ∣ w i := by
    intro p h hc hp hh h5
    by_contra hnd
    push Not at hnd
    obtain ⟨t, ht, hfar⟩ := LRC.prime_case hc hp hh h5 w hE hT hnd
    refine hcon ⟨t, ht, fun i => ?_⟩
    have h6 : (1 : ℝ) / ((5 + 1 : ℕ) : ℝ) = 1 / 6 := by norm_num
    have h7 := hfar i
    unfold LRC.far at h7
    rw [Int.cast_natCast] at h7
    rw [ge_iff_le, h6]
    exact h7
  have hd : ∀ i, w i ∣ ∏ i, w i := fun i => Finset.dvd_prod_of_mem w (Finset.mem_univ i)
  obtain ⟨_, q4⟩ := hsieve 4 (by norm_num) (by norm_num)
  obtain ⟨_, q3⟩ := hsieve 3 (by norm_num) (by norm_num)
  obtain ⟨_, q5⟩ := hsieve 5 (by norm_num) (by norm_num)
  obtain ⟨_, q29⟩ := key 29 14 LRC.chk29 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, q31⟩ := key 31 15 LRC.chk31 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, q37⟩ := key 37 18 LRC.chk37 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, q41⟩ := key 41 20 LRC.chk41 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, q43⟩ := key 43 21 LRC.chk43 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, q47⟩ := key 47 23 LRC.chk47 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, q53⟩ := key 53 26 LRC.chk53 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, q59⟩ := key 59 29 LRC.chk59 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, q61⟩ := key 61 30 LRC.chk61 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, q67⟩ := key 67 33 LRC.chk67 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, q71⟩ := key 71 35 LRC.chk71 (by norm_num) (by norm_num) (by norm_num)
  have d1 : 4 * 3 ∣ ∏ i, w i :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (q4.trans (hd _)) (q3.trans (hd _))
  have d2 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d1 (q5.trans (hd _))
  have d3 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d2 (q29.trans (hd _))
  have d4 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d3 (q31.trans (hd _))
  have d5 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d4 (q37.trans (hd _))
  have d6 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d5 (q41.trans (hd _))
  have d7 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d6 (q43.trans (hd _))
  have d8 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d7 (q47.trans (hd _))
  have d9 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d8 (q53.trans (hd _))
  have d10 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d9 (q59.trans (hd _))
  have d11 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d10 (q61.trans (hd _))
  have d12 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d11 (q67.trans (hd _))
  have d13 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d12 (q71.trans (hd _))
  have hPpos : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hpos i)
  have hQ : 150056117022484571820 ≤ ∏ i, w i := by
    have h1 := Nat.le_of_dvd hPpos d13
    norm_num at h1
    exact h1
  have hS : ∑ i, w i ≤ 50625 := by
    have h1 : ∑ i : Fin 5, w i ≤ ∑ S ∈ (Finset.univ : Finset (Fin 5)).powerset.erase ∅, S.gcd w := by
      calc ∑ i : Fin 5, w i
          = ∑ S ∈ Finset.univ.image (fun i : Fin 5 => ({i} : Finset (Fin 5))), S.gcd w := by
            rw [Finset.sum_image (fun a _ b _ hab => Finset.singleton_injective hab)]
            exact Finset.sum_congr rfl (fun i _ => by simp)
        _ ≤ _ := Finset.sum_le_sum_of_subset (by
            intro S hS
            obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hS
            simp)
    have h2 : (Nat.choose 6 2) ^ 4 = 50625 := by decide
    omega
  have hA := LRC.amgm5 (fun i => (w i : ℝ)) (fun i => by positivity)
  have hQ' : (150056117022484571820 : ℝ) ≤ ∏ i, (w i : ℝ) := by exact_mod_cast hQ
  have hS' : ∑ i, (w i : ℝ) ≤ 50625 := by exact_mod_cast hS
  have hS0 : (0 : ℝ) ≤ ∑ i, (w i : ℝ) := Finset.sum_nonneg (fun i _ => by positivity)
  have hB : ((∑ i, (w i : ℝ)) / 5) ^ 5 ≤ ((50625 : ℝ) / 5) ^ 5 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 5
  norm_num at hB
  linarith
