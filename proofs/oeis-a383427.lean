import OMAStatements.S_oeis_a383427

-- Problem: A383427: Indices k such that A003849(k) = A383422(k).
-- Upstream: formal-conjectures statements/oeis-a383427.lean:0 (declaration OMA.S_oeis_a383427.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let s = sqrt 5, psi = (s - 1)/2, g n = floor (n * psi), x k = fract ((k + 1) * (5 - s)/10).
-- By induction on prefixes, A003849(k) = 0 iff g (k + 2) = g (k + 1) + 1, and since the Lucas word is
-- the image of the Fibonacci word under 0 -> 0, 1 -> 11, A383422(k) = 0 iff x k < s/5.
-- Both letters depend only on which subinterval of (0, 1) contains x k, so the target indices are
-- the k with x k in finitely many explicit intervals; rotation by (5 - s)/10 shows that every gap
-- lies in the stated set, and explicit small witnesses (checked on fibIter 9 and lucasIter 8) show
-- that all of them occur. The real constants are carried by the structure Wd, built from
-- Real.sqrt 5 at the end.

namespace ProofA383427

open OMA.S_oeis_a383427

-- s = sqrt 5, g n = floor (n * (s - 1) / 2), x k = fract ((k + 1) * (5 - s) / 10),
-- bl k = 0 if x k < s / 5 and 1 otherwise.
structure Wd where
  s : ℝ
  g : ℕ → ℕ
  x : ℕ → ℝ
  bl : ℕ → ℕ
  hs : s ^ 2 = 5
  hpos : 0 < s
  hg : ∀ n : ℕ, g n = ⌊(n : ℝ) * ((s - 1) / 2)⌋₊
  hx : ∀ k : ℕ, x k = Int.fract (((k : ℝ) + 1) * ((5 - s) / 10))
  hbl : ∀ k : ℕ, bl k = if x k < s / 5 then 0 else 1

theorem Wd_nonempty : Nonempty Wd :=
  ⟨⟨Real.sqrt 5, fun n => ⌊(n : ℝ) * ((Real.sqrt 5 - 1) / 2)⌋₊,
    fun k => Int.fract (((k : ℝ) + 1) * ((5 - Real.sqrt 5) / 10)),
    fun k => if Int.fract (((k : ℝ) + 1) * ((5 - Real.sqrt 5) / 10)) < Real.sqrt 5 / 5 then 0 else 1,
    Real.sq_sqrt (by norm_num), Real.sqrt_pos.mpr (by norm_num),
    fun _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩

theorem s_lo (W : Wd) : (223606 : ℝ) / 100000 < W.s := by
  nlinarith [W.hs, W.hpos]

theorem s_hi (W : Wd) : W.s < (223607 : ℝ) / 100000 := by
  nlinarith [W.hs, W.hpos]

theorem psi_pos (W : Wd) : 0 < (W.s - 1) / 2 := by linarith [s_lo W]

theorem psi_lt_one (W : Wd) : (W.s - 1) / 2 < 1 := by linarith [s_hi W]

theorem sq_ne_five_mul_sq : ∀ b a : ℕ, 0 < b → a ^ 2 ≠ 5 * b ^ 2 := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a hb h
    have h5 : 5 ∣ a := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow ⟨b ^ 2, h⟩
    obtain ⟨c, rfl⟩ := h5
    have hbc : b ^ 2 = 5 * c ^ 2 := by nlinarith
    have hc0 : 0 < c := by nlinarith
    have hcb : c < b := by nlinarith
    exact ih c hcb b hc0 hbc

theorem s_irr (W : Wd) (p q : ℤ) (hq : q ≠ 0) : (p : ℝ) ≠ (q : ℝ) * W.s := by
  intro heq
  have hsq : (p : ℝ) ^ 2 = ((q : ℝ) * W.s) ^ 2 := congrArg (· ^ 2) heq
  rw [mul_pow, W.hs] at hsq
  have hzi : p ^ 2 = 5 * q ^ 2 := by exact_mod_cast (by linarith : (p : ℝ) ^ 2 = 5 * (q : ℝ) ^ 2)
  have hnat : p.natAbs ^ 2 = 5 * q.natAbs ^ 2 := by
    have hp : ((p.natAbs ^ 2 : ℕ) : ℤ) = p ^ 2 := by rw [Nat.cast_pow, Int.natAbs_sq]
    have hq' : ((q.natAbs ^ 2 : ℕ) : ℤ) = q ^ 2 := by rw [Nat.cast_pow, Int.natAbs_sq]
    exact_mod_cast (by linarith : ((p.natAbs ^ 2 : ℕ) : ℤ) = 5 * ((q.natAbs ^ 2 : ℕ) : ℤ))
  exact sq_ne_five_mul_sq q.natAbs p.natAbs (Int.natAbs_pos.mpr hq) hnat

-- Part 0: the rotation x and the Beatty floor g

theorem x_floor (W : Wd) (k : ℕ) :
    ∃ C : ℤ, W.x k = ((k : ℝ) + 1) * ((5 - W.s) / 10) - (C : ℝ) :=
  ⟨⌊((k : ℝ) + 1) * ((5 - W.s) / 10)⌋,
    (W.hx k).trans (Int.self_sub_floor (((k : ℝ) + 1) * ((5 - W.s) / 10))).symm⟩

theorem x_eq_of (W : Wd) (k : ℕ) (n : ℤ) (y : ℝ)
    (h : ((k : ℝ) + 1) * ((5 - W.s) / 10) = (n : ℝ) + y) (h0 : 0 ≤ y) (h1 : y < 1) :
    W.x k = y := by
  rw [W.hx, h, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨h0, h1⟩]

theorem x_ne (W : Wd) (k : ℕ) (p : ℤ) (q : ℕ) :
    W.x k ≠ ((p : ℝ) + (q : ℝ) * W.s) / 10 := by
  intro h
  obtain ⟨C, hC⟩ := x_floor W k
  have e : ((k : ℝ) + 1) * ((5 - W.s) / 10) - (C : ℝ) = ((p : ℝ) + (q : ℝ) * W.s) / 10 :=
    hC.symm.trans h
  have hlin : ((5 * ((k : ℤ) + 1) - 10 * C - p : ℤ) : ℝ) =
      (((k : ℤ) + 1 + (q : ℤ) : ℤ) : ℝ) * W.s := by
    push_cast
    linear_combination 10 * e
  exact s_irr W _ _ (by omega) hlin

theorem x_pos (W : Wd) (k : ℕ) : 0 < W.x k := by
  have hge : 0 ≤ W.x k := by rw [W.hx]; exact Int.fract_nonneg _
  have hne := x_ne W k 0 0
  push_cast at hne
  have hne0 : W.x k ≠ 0 := by intro h; exact hne (by linarith)
  exact lt_of_le_of_ne hge (Ne.symm hne0)

theorem x_shift (W : Wd) (k d : ℕ) (c : ℤ)
    (hlo : (c : ℝ) < W.x k + (d : ℝ) * ((5 - W.s) / 10))
    (hhi : W.x k + (d : ℝ) * ((5 - W.s) / 10) < (c : ℝ) + 1) :
    W.x (k + d) = W.x k + (d : ℝ) * ((5 - W.s) / 10) - (c : ℝ) := by
  obtain ⟨C, hC⟩ := x_floor W k
  apply x_eq_of W (k + d) (C + c)
  · push_cast
    rw [hC]
    ring
  · linarith
  · linarith

theorem g_le (W : Wd) (n : ℕ) : (W.g n : ℝ) ≤ (n : ℝ) * ((W.s - 1) / 2) := by
  rw [W.hg n]
  exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (psi_pos W).le)

theorem g_lt (W : Wd) (n : ℕ) : (n : ℝ) * ((W.s - 1) / 2) < (W.g n : ℝ) + 1 := by
  rw [W.hg n]
  exact Nat.lt_floor_add_one _

theorem g_lt' (W : Wd) (n : ℕ) (hn : 0 < n) : (W.g n : ℝ) < (n : ℝ) * ((W.s - 1) / 2) := by
  rcases lt_or_eq_of_le (g_le W n) with h | h
  · exact h
  · exfalso
    have h2 : ((2 * (W.g n : ℤ) + (n : ℤ) : ℤ) : ℝ) = ((n : ℤ) : ℝ) * W.s := by
      push_cast
      linear_combination 2 * h
    exact s_irr W _ _ (by omega) h2

theorem g_eq (W : Wd) (n t : ℕ) (h1 : (t : ℝ) ≤ (n : ℝ) * ((W.s - 1) / 2))
    (h2 : (n : ℝ) * ((W.s - 1) / 2) < (t : ℝ) + 1) : W.g n = t := by
  rw [W.hg n, Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg n) (psi_pos W).le)]
  exact ⟨h1, h2⟩

theorem g_eq_int (W : Wd) (n : ℕ) (t : ℤ) (h1 : (t : ℝ) ≤ (n : ℝ) * ((W.s - 1) / 2))
    (h2 : (n : ℝ) * ((W.s - 1) / 2) < (t : ℝ) + 1) : (W.g n : ℤ) = t := by
  have a1 := g_le W n
  have a2 := g_lt W n
  have b1 : ((W.g n : ℤ) : ℝ) < (t : ℝ) + 1 := by push_cast; linarith
  have b2 : (t : ℝ) < ((W.g n : ℤ) : ℝ) + 1 := by push_cast; linarith
  have c1 : (W.g n : ℤ) < t + 1 := by exact_mod_cast b1
  have c2 : t < (W.g n : ℤ) + 1 := by exact_mod_cast b2
  omega

theorem g_succ (W : Wd) (n : ℕ) : W.g (n + 1) = W.g n ∨ W.g (n + 1) = W.g n + 1 := by
  have a1 := g_le W n
  have a2 := g_lt W n
  have b1 := g_le W (n + 1)
  have b2 := g_lt W (n + 1)
  push_cast at b1 b2
  have hp := psi_pos W
  have hp1 := psi_lt_one W
  have c1 : (W.g n : ℝ) < (W.g (n + 1) : ℝ) + 1 := by linarith
  have c2 : (W.g (n + 1) : ℝ) < (W.g n : ℝ) + 2 := by linarith
  have d1 : W.g n < W.g (n + 1) + 1 := by exact_mod_cast c1
  have d2 : W.g (n + 1) < W.g n + 2 := by exact_mod_cast c2
  omega

theorem g_le_self (W : Wd) (m : ℕ) : W.g (m + 1) ≤ m := by
  have a1 := g_le W (m + 1)
  push_cast at a1
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have e := mul_le_mul_of_nonneg_left (s_hi W).le hm
  have c : (W.g (m + 1) : ℝ) < (m : ℝ) + 1 := by linarith [s_lo W, s_hi W]
  have d : W.g (m + 1) < m + 1 := by exact_mod_cast c
  omega

theorem g_one' (W : Wd) : W.g (0 + 1) = 0 :=
  g_eq W (0 + 1) 0 (by push_cast; linarith [psi_pos W]) (by push_cast; linarith [psi_lt_one W])

theorem g_two' (W : Wd) : W.g (0 + 2) = 1 :=
  g_eq W (0 + 2) 1 (by push_cast; linarith [s_lo W]) (by push_cast; linarith [s_hi W])

theorem g_key (W : Wd) (m : ℕ) :
    W.g (m + 1 + W.g (m + 1)) = m ∧ W.g (m + 2 + W.g (m + 1)) = m + 1 := by
  have h1 := g_lt' W (m + 1) (by omega)
  have h2 := g_lt W (m + 1)
  push_cast at h1 h2
  have hp := psi_pos W
  have hp1 := psi_lt_one W
  have e1 := mul_lt_mul_of_pos_right h1 hp
  have e2 := mul_lt_mul_of_pos_right h2 hp
  have hm5 : (m : ℝ) * W.s ^ 2 = 5 * (m : ℝ) := by linear_combination (m : ℝ) * W.hs
  have hs5 := W.hs
  constructor
  · apply g_eq
    · push_cast
      linarith
    · push_cast
      linarith
  · apply g_eq
    · push_cast
      linarith
    · push_cast
      linarith

theorem psi_to_phi (W : Wd) {a b : ℝ} (h : a * ((W.s - 1) / 2) < b) :
    2 * a < b * (W.s + 1) := by
  have hp : (0 : ℝ) < W.s + 1 := by linarith [W.hpos]
  have e := mul_lt_mul_of_pos_right h hp
  have e2 : a * ((W.s - 1) / 2) * (W.s + 1) = 2 * a := by
    linear_combination (a / 2) * W.hs
  linarith

theorem psi_to_phi' (W : Wd) {a b : ℝ} (h : b < a * ((W.s - 1) / 2)) :
    b * (W.s + 1) < 2 * a := by
  have hp : (0 : ℝ) < W.s + 1 := by linarith [W.hpos]
  have e := mul_lt_mul_of_pos_right h hp
  have e2 : a * ((W.s - 1) / 2) * (W.s + 1) = 2 * a := by
    linear_combination (a / 2) * W.hs
  linarith

-- Part 1: Fibonacci word prefix and Beatty characterization

theorem fibStep_append (l1 l2 : List ℕ) : fibStep (l1 ++ l2) = fibStep l1 ++ fibStep l2 := by
  induction l1 with
  | nil => rfl
  | cons a l ih =>
    cases a with
    | zero =>
      show 0 :: 1 :: fibStep (l ++ l2) = 0 :: 1 :: (fibStep l ++ fibStep l2)
      rw [ih]
    | succ m =>
      show 0 :: fibStep (l ++ l2) = 0 :: (fibStep l ++ fibStep l2)
      rw [ih]

theorem fibIter_add2 : ∀ n : ℕ, fibIter (n + 2) = fibIter (n + 1) ++ fibIter n
  | 0 => rfl
  | n + 1 => by
    show fibStep (fibIter (n + 2)) = fibStep (fibIter (n + 1)) ++ fibStep (fibIter n)
    rw [fibIter_add2 n, fibStep_append]

theorem fibIter_len_ge : ∀ n : ℕ, n + 1 ≤ (fibIter n).length
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    rw [fibIter_add2, List.length_append]
    have h1 := fibIter_len_ge (n + 1)
    have h0 := fibIter_len_ge n
    omega

theorem fibIter_getD_succ (n k : ℕ) (h : k < (fibIter n).length) :
    (fibIter (n + 1)).getD k 0 = (fibIter n).getD k 0 := by
  cases n with
  | zero =>
    have hk : k = 0 := by
      have hlen : (fibIter 0).length = 1 := rfl
      omega
    subst hk; rfl
  | succ m =>
    rw [fibIter_add2, List.getD_eq_getElem?_getD, List.getElem?_append_left h,
      ← List.getD_eq_getElem?_getD]

theorem fibIter_getD_le (n m k : ℕ) (hnm : n ≤ m) (h : k < (fibIter n).length) :
    (fibIter m).getD k 0 = (fibIter n).getD k 0 := by
  induction hnm with
  | refl => rfl
  | @step m hnm ih =>
    have hlt : k < (fibIter m).length := by
      have hmono : ∀ a b, a ≤ b → (fibIter a).length ≤ (fibIter b).length := by
        intro a b hab
        induction hab with
        | refl => exact le_refl _
        | @step b hab ihb =>
          cases b with
          | zero => exact le_trans ihb (by decide)
          | succ b' =>
            rw [fibIter_add2, List.length_append]
            omega
      exact lt_of_lt_of_le h (hmono n m hnm)
    rw [fibIter_getD_succ m k hlt, ih]

theorem A003849_eq_of_lt (n k : ℕ) (h : k < (fibIter n).length) :
    A003849 k = (fibIter n).getD k 0 := by
  unfold A003849
  rcases le_total n (k + 1) with hle | hle
  · exact fibIter_getD_le n (k + 1) k hle h
  · have hk : k < (fibIter (k + 1)).length := by have := fibIter_len_ge (k + 1); omega
    exact (fibIter_getD_le (k + 1) n k hle hk).symm

def B (W : Wd) (k : ℕ) : ℕ := if W.g (k + 2) = W.g (k + 1) + 1 then 0 else 1

def SB (W : Wd) (m : ℕ) : List ℕ := (List.range m).map (B W)

theorem SB_succ (W : Wd) (m : ℕ) : SB W (m + 1) = SB W m ++ [B W m] := by
  unfold SB; rw [List.range_succ, List.map_append]; rfl

theorem B_key (W : Wd) (m : ℕ) : B W (m + W.g (m + 1)) = 0 := by
  obtain ⟨k1, k2⟩ := g_key W m
  unfold B
  rw [show m + W.g (m + 1) + 2 = m + 2 + W.g (m + 1) by omega,
    show m + W.g (m + 1) + 1 = m + 1 + W.g (m + 1) by omega, k1, k2]
  exact if_pos rfl

theorem B_key2 (W : Wd) (m : ℕ) (hi : W.g (m + 2) = W.g (m + 1) + 1) :
    B W (m + W.g (m + 1) + 1) = 1 := by
  have k2 := (g_key W m).2
  have k3 : W.g (m + 2 + W.g (m + 2)) = m + 1 := (g_key W (m + 1)).1
  rw [hi] at k3
  unfold B
  rw [show m + W.g (m + 1) + 1 + 2 = m + 2 + (W.g (m + 1) + 1) by omega,
    show m + W.g (m + 1) + 1 + 1 = m + 2 + W.g (m + 1) by omega, k3, k2]
  exact if_neg (by omega)

theorem fibStep_SB (W : Wd) (m : ℕ) : fibStep (SB W m) = SB W (m + W.g (m + 1)) := by
  induction m with
  | zero =>
    rw [g_one' W]
    rfl
  | succ m ih =>
    have hsucc : W.g (m + 2) = W.g (m + 1) ∨ W.g (m + 2) = W.g (m + 1) + 1 := g_succ W (m + 1)
    rw [SB_succ, fibStep_append, ih, show m + 1 + 1 = m + 2 from rfl]
    rcases hsucc with hs | hi
    · have hne : ¬ (W.g (m + 2) = W.g (m + 1) + 1) := by omega
      have hBm : B W m = 1 := by unfold B; rw [if_neg hne]
      rw [hBm, hs, show m + 1 + W.g (m + 1) = m + W.g (m + 1) + 1 by omega, SB_succ, B_key W m]
      rfl
    · have hBm : B W m = 0 := by unfold B; rw [if_pos hi]
      rw [hBm, hi, show m + 1 + (W.g (m + 1) + 1) = m + W.g (m + 1) + 1 + 1 by omega, SB_succ,
        SB_succ, B_key W m, B_key2 W m hi, List.append_assoc]
      rfl

theorem fibIter_eq_SB (W : Wd) : ∀ n : ℕ, ∃ m : ℕ, fibIter n = SB W m
  | 0 => ⟨0 + 1, by
      have hB0 : B W 0 = 0 := by
        unfold B
        rw [g_two' W, g_one' W]
        exact if_pos rfl
      rw [SB_succ, hB0]
      rfl⟩
  | n + 1 => by
    obtain ⟨m, hm⟩ := fibIter_eq_SB W n
    exact ⟨m + W.g (m + 1), by show fibStep (fibIter n) = _; rw [hm, fibStep_SB]⟩

theorem getD_map_range (f : ℕ → ℕ) (N k : ℕ) (hk : k < N) :
    ((List.range N).map f).getD k 0 = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem A003849_eq_B (W : Wd) (k : ℕ) : A003849 k = B W k := by
  obtain ⟨m, hm⟩ := fibIter_eq_SB W (k + 1)
  have hlen : k < (SB W m).length := by
    rw [← hm]; have := fibIter_len_ge (k + 1); omega
  have hkm : k < m := by simpa [SB] using hlen
  unfold A003849
  rw [hm]
  exact getD_map_range (B W) m k hkm

-- Part 2: Lucas word prefix and fractional-part characterization

def doubleOnes : List ℕ → List ℕ
  | [] => []
  | 0 :: rest => 0 :: doubleOnes rest
  | _ :: rest => 1 :: 1 :: doubleOnes rest

theorem doubleOnes_append (l1 l2 : List ℕ) :
    doubleOnes (l1 ++ l2) = doubleOnes l1 ++ doubleOnes l2 := by
  induction l1 with
  | nil => rfl
  | cons a l ih =>
    cases a with
    | zero =>
      show 0 :: doubleOnes (l ++ l2) = 0 :: (doubleOnes l ++ doubleOnes l2)
      rw [ih]
    | succ m =>
      show 1 :: 1 :: doubleOnes (l ++ l2) = 1 :: 1 :: (doubleOnes l ++ doubleOnes l2)
      rw [ih]

theorem lucasIter_eq_doubleOnes : ∀ n : ℕ, lucasIter n = doubleOnes (fibIter n)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    show lucasIter (n + 1) ++ lucasIter n = doubleOnes (fibIter (n + 2))
    rw [lucasIter_eq_doubleOnes (n + 1), lucasIter_eq_doubleOnes n,
      ← doubleOnes_append, fibIter_add2]

theorem lucasIter_len_ge : ∀ n : ℕ, n + 1 ≤ (lucasIter n).length
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    show n + 3 ≤ (lucasIter (n + 1) ++ lucasIter n).length
    rw [List.length_append]
    have h1 := lucasIter_len_ge (n + 1)
    have h0 := lucasIter_len_ge n
    omega

theorem lucasIter_getD_succ (n k : ℕ) (h : k < (lucasIter n).length) :
    (lucasIter (n + 1)).getD k 0 = (lucasIter n).getD k 0 := by
  cases n with
  | zero =>
    have hk : k = 0 := by
      have hlen : (lucasIter 0).length = 1 := rfl
      omega
    subst hk; rfl
  | succ m =>
    show (lucasIter (m + 1) ++ lucasIter m).getD k 0 = (lucasIter (m + 1)).getD k 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

theorem lucasIter_getD_le (n m k : ℕ) (hnm : n ≤ m) (h : k < (lucasIter n).length) :
    (lucasIter m).getD k 0 = (lucasIter n).getD k 0 := by
  induction hnm with
  | refl => rfl
  | @step m hnm ih =>
    have hlt : k < (lucasIter m).length := by
      have hmono : ∀ a b, a ≤ b → (lucasIter a).length ≤ (lucasIter b).length := by
        intro a b hab
        induction hab with
        | refl => exact le_refl _
        | @step b hab ihb =>
          cases b with
          | zero => exact le_trans ihb (by decide)
          | succ b' =>
            show (lucasIter a).length ≤ (lucasIter (b' + 1) ++ lucasIter b').length
            rw [List.length_append]; omega
      exact lt_of_lt_of_le h (hmono n m hnm)
    rw [lucasIter_getD_succ m k hlt, ih]

theorem A383422_eq_of_lt (n k : ℕ) (h : k < (lucasIter n).length) :
    A383422 k = (lucasIter n).getD k 0 := by
  unfold A383422
  rcases le_total n k with hle | hle
  · exact lucasIter_getD_le n k k hle h
  · have hk : k < (lucasIter k).length := by have := lucasIter_len_ge k; omega
    exact (lucasIter_getD_le k n k hle hk).symm

def SL (W : Wd) (m : ℕ) : List ℕ := (List.range m).map W.bl

theorem SL_succ (W : Wd) (m : ℕ) : SL W (m + 1) = SL W m ++ [W.bl m] := by
  unfold SL; rw [List.range_succ, List.map_append]; rfl

theorem doubleOnes_SB (W : Wd) (m : ℕ) :
    doubleOnes (SB W m) = SL W (2 * m - W.g (m + 1)) := by
  induction m with
  | zero =>
    rw [g_one' W]
    rfl
  | succ m ih =>
    have hsucc : W.g (m + 2) = W.g (m + 1) ∨ W.g (m + 2) = W.g (m + 1) + 1 := g_succ W (m + 1)
    have hq_le : W.g (m + 1) ≤ m := g_le_self W m
    obtain ⟨P0, hP0⟩ : ∃ P0 : ℕ, P0 + W.g (m + 1) = 2 * m := ⟨2 * m - W.g (m + 1), by omega⟩
    rw [SB_succ, doubleOnes_append, ih, show m + 1 + 1 = m + 2 from rfl,
      show 2 * m - W.g (m + 1) = P0 by omega]
    have hP0R : (P0 : ℝ) + (W.g (m + 1) : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hP0
    have hP0R' : (P0 : ℝ) = 2 * (m : ℝ) - (W.g (m + 1) : ℝ) := by linarith
    have h1 := g_lt' W (m + 1) (by omega)
    have h2 := g_lt W (m + 1)
    push_cast at h1 h2
    have F1 := psi_to_phi' W h1
    have F2 := psi_to_phi W h2
    have hsl := s_lo W
    have hsh := s_hi W
    have hs5 := W.hs
    obtain ⟨y, hy⟩ : ∃ y : ℝ,
        y = ((W.g (m + 1) : ℝ) + 1) * (5 + W.s) / 10 - ((m : ℝ) + 1) * W.s / 5 := ⟨_, rfl⟩
    have hys : y * W.s = ((W.g (m + 1) : ℝ) + 1) * (W.s + 1) / 2 - ((m : ℝ) + 1) := by
      rw [hy]
      linear_combination (((W.g (m + 1) : ℝ) + 1) / 10 - ((m : ℝ) + 1) / 5) * W.hs
    have hy0 : 0 < y := by
      have hz : 0 < y * W.s := by rw [hys]; linarith
      exact pos_of_mul_pos_left hz W.hpos.le
    have hy1 : y < 1 := by
      have hz : 0 < (1 - y) * W.s := by linarith
      have := pos_of_mul_pos_left hz W.hpos.le
      linarith
    have hxP0 : W.x P0 = y := by
      apply x_eq_of W P0 ((m : ℤ) - (W.g (m + 1) : ℤ))
      · rw [hP0R', hy]
        push_cast
        ring
      · exact hy0.le
      · exact hy1
    rcases hsucc with hs | hi
    · have hne : ¬ (W.g (m + 2) = W.g (m + 1) + 1) := by omega
      have hBm : B W m = 1 := by unfold B; rw [if_neg hne]
      have h3 := g_lt W (m + 2)
      rw [hs] at h3
      push_cast at h3
      have F3 := psi_to_phi W h3
      have hc : W.s / 5 < y := by
        have hz : 0 < (y - W.s / 5) * W.s := by linarith
        have := pos_of_mul_pos_left hz W.hpos.le
        linarith
      have hd : y < (5 + W.s) / 10 := by
        have hz : 0 < ((5 + W.s) / 10 - y) * W.s := by linarith
        have := pos_of_mul_pos_left hz W.hpos.le
        linarith
      have hxP1 : W.x (P0 + 1) = y + (5 - W.s) / 10 := by
        apply x_eq_of W (P0 + 1) ((m : ℤ) - (W.g (m + 1) : ℤ))
        · push_cast
          rw [hP0R', hy]
          ring
        · linarith
        · linarith
      have hn1 : ¬ (y + (5 - W.s) / 10 < W.s / 5) := by
        intro h
        linarith
      have hbl0 : W.bl P0 = 1 := by
        rw [W.hbl, hxP0, if_neg (not_lt.mpr hc.le)]
      have hbl1 : W.bl (P0 + 1) = 1 := by
        rw [W.hbl, hxP1, if_neg hn1]
      rw [hBm, show 2 * (m + 1) - W.g (m + 2) = P0 + 1 + 1 by omega, SL_succ, SL_succ, hbl0,
        hbl1, List.append_assoc]
      rfl
    · have hBm : B W m = 0 := by unfold B; rw [if_pos hi]
      have h3 := g_lt' W (m + 2) (by omega)
      rw [hi] at h3
      push_cast at h3
      have F3 := psi_to_phi' W h3
      have he : y < W.s / 5 := by
        have hz : 0 < (W.s / 5 - y) * W.s := by linarith
        have := pos_of_mul_pos_left hz W.hpos.le
        linarith
      have hbl0 : W.bl P0 = 0 := by
        rw [W.hbl, hxP0, if_pos he]
      rw [hBm, show 2 * (m + 1) - W.g (m + 2) = P0 + 1 by omega, SL_succ, hbl0]
      rfl

theorem A383422_eq_BL (W : Wd) (k : ℕ) : A383422 k = W.bl k := by
  obtain ⟨m, hm⟩ := fibIter_eq_SB W k
  have hluc : lucasIter k = SL W (2 * m - W.g (m + 1)) := by
    rw [lucasIter_eq_doubleOnes, hm, doubleOnes_SB]
  have hlen : k < (SL W (2 * m - W.g (m + 1))).length := by
    rw [← hluc]; have := lucasIter_len_ge k; omega
  have hkm : k < 2 * m - W.g (m + 1) := by simpa [SL] using hlen
  unfold A383422
  rw [hluc]
  exact getD_map_range W.bl _ k hkm

-- Part 3: Express both A003849 and A383422 in terms of x k

theorem A383422_eq_zero_iff (W : Wd) (k : ℕ) : A383422 k = 0 ↔ W.x k < W.s / 5 := by
  rw [A383422_eq_BL W, W.hbl]
  split_ifs with h <;> simp [h]

theorem B_zero_iff (W : Wd) (k : ℕ) :
    B W k = 0 ↔ 1 - (W.s - 1) / 2 < ((k : ℝ) + 1) * ((W.s - 1) / 2) - (W.g (k + 1) : ℝ) := by
  have a2 := g_lt W (k + 1)
  have b1 := g_lt' W (k + 2) (by omega)
  push_cast at a2 b1
  have hp1 := psi_lt_one W
  unfold B
  constructor
  · intro h
    have heq : W.g (k + 2) = W.g (k + 1) + 1 := by
      by_contra hne
      rw [if_neg hne] at h
      exact absurd h one_ne_zero
    rw [heq] at b1
    push_cast at b1
    linarith
  · intro h
    have heq : W.g (k + 2) = W.g (k + 1) + 1 := by
      apply g_eq
      · push_cast
        linarith
      · push_cast
        linarith
    rw [if_pos heq]

theorem frac_of_region (W : Wd) (k j : ℕ)
    (hlo : 2 * (j : ℝ) / 10 < W.x k) (hhi : W.x k < (2 * (j : ℝ) + 2) / 10) :
    ((k : ℝ) + 1) * ((W.s - 1) / 2) - (W.g (k + 1) : ℝ) = (j : ℝ) + 1 - 5 * W.x k := by
  obtain ⟨C, hC⟩ := x_floor W k
  have hT : (W.g (k + 1) : ℤ) = 2 * ((k : ℤ) + 1) - 5 * C - (j : ℤ) - 1 := by
    apply g_eq_int W (k + 1)
    · push_cast
      linarith
    · push_cast
      linarith
  have hTR : (W.g (k + 1) : ℝ) = 2 * ((k : ℝ) + 1) - 5 * (C : ℝ) - (j : ℝ) - 1 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hT
    push_cast at h
    linarith
  rw [hTR, hC]
  ring

theorem x_lt_one (W : Wd) (k : ℕ) : W.x k < 1 := by
  rw [W.hx]
  exact Int.fract_lt_one _

theorem A383422_zero_or_one (W : Wd) (k : ℕ) : A383422 k = 0 ∨ A383422 k = 1 := by
  rw [A383422_eq_BL W, W.hbl]; split_ifs <;> simp

theorem A003849_zero_or_one (W : Wd) (k : ℕ) : A003849 k = 0 ∨ A003849 k = 1 := by
  rw [A003849_eq_B W]; unfold B; split_ifs <;> simp

theorem A383422_eq_one_iff (W : Wd) (k : ℕ) : A383422 k = 1 ↔ W.s / 5 < W.x k := by
  rw [A383422_eq_BL W, W.hbl]
  have hne : W.x k ≠ W.s / 5 := by
    have h0 := x_ne W k 0 2
    push_cast at h0
    intro h; exact h0 (by linarith)
  split_ifs with h
  · constructor
    · intro hc; norm_num at hc
    · intro hlt; linarith
  · constructor
    · intro _; exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)
    · intro _; rfl

theorem A003849_eq_zero_iff (W : Wd) (k : ℕ) :
    A003849 k = 0 ↔
      ((((0 : ℝ) + (0 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((-1 : ℝ) + (1 : ℝ) * W.s) / 10) ∨
       (((2 : ℝ) + (0 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((1 : ℝ) + (1 : ℝ) * W.s) / 10) ∨
       (((4 : ℝ) + (0 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((3 : ℝ) + (1 : ℝ) * W.s) / 10) ∨
       (((6 : ℝ) + (0 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((5 : ℝ) + (1 : ℝ) * W.s) / 10) ∨
       (((8 : ℝ) + (0 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((7 : ℝ) + (1 : ℝ) * W.s) / 10)) := by
  rw [A003849_eq_B W, B_zero_iff W]
  have h0 := x_pos W k
  have h1 := x_lt_one W k
  have hsl := s_lo W
  have hsh := s_hi W
  have hne2 : W.x k ≠ (2 : ℝ) / 10 := by
    have h := x_ne W k 2 0; push_cast at h; intro e; exact h (by linarith)
  have hne4 : W.x k ≠ (4 : ℝ) / 10 := by
    have h := x_ne W k 4 0; push_cast at h; intro e; exact h (by linarith)
  have hne6 : W.x k ≠ (6 : ℝ) / 10 := by
    have h := x_ne W k 6 0; push_cast at h; intro e; exact h (by linarith)
  have hne8 : W.x k ≠ (8 : ℝ) / 10 := by
    have h := x_ne W k 8 0; push_cast at h; intro e; exact h (by linarith)
  rcases lt_or_gt_of_ne hne2 with c1 | c1
  · have hf := frac_of_region W k 0 (by push_cast; linarith) (by push_cast; linarith)
    push_cast at hf
    constructor
    · intro hA
      exact Or.inl ⟨by linarith, by linarith⟩
    · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩) <;> linarith
  · rcases lt_or_gt_of_ne hne4 with c2 | c2
    · have hf := frac_of_region W k 1 (by push_cast; linarith) (by push_cast; linarith)
      push_cast at hf
      constructor
      · intro hA
        exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩) <;> linarith
    · rcases lt_or_gt_of_ne hne6 with c3 | c3
      · have hf := frac_of_region W k 2 (by push_cast; linarith) (by push_cast; linarith)
        push_cast at hf
        constructor
        · intro hA
          exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
        · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩) <;> linarith
      · rcases lt_or_gt_of_ne hne8 with c4 | c4
        · have hf := frac_of_region W k 3 (by push_cast; linarith) (by push_cast; linarith)
          push_cast at hf
          constructor
          · intro hA
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩)))
          · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩) <;> linarith
        · have hf := frac_of_region W k 4 (by push_cast; linarith) (by push_cast; linarith)
          push_cast at hf
          constructor
          · intro hA
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩)))
          · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩) <;> linarith

theorem A003849_eq_one_iff (W : Wd) (k : ℕ) :
    A003849 k = 1 ↔
      ((((-1 : ℝ) + (1 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((2 : ℝ) + (0 : ℝ) * W.s) / 10) ∨
       (((1 : ℝ) + (1 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((4 : ℝ) + (0 : ℝ) * W.s) / 10) ∨
       (((3 : ℝ) + (1 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((6 : ℝ) + (0 : ℝ) * W.s) / 10) ∨
       (((5 : ℝ) + (1 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((8 : ℝ) + (0 : ℝ) * W.s) / 10) ∨
       (((7 : ℝ) + (1 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((10 : ℝ) + (0 : ℝ) * W.s) / 10)) := by
  have h01 : A003849 k = 1 ↔ ¬ (A003849 k = 0) := by
    rcases A003849_zero_or_one W k with h | h <;> simp [h]
  rw [h01, A003849_eq_zero_iff W]
  have h0 := x_pos W k
  have h1 := x_lt_one W k
  have hsl := s_lo W
  have hsh := s_hi W
  have hne_f0 := x_ne W k (-1) 1
  push_cast at hne_f0
  have hne_f1 := x_ne W k 1 1
  push_cast at hne_f1
  have hne_f2 := x_ne W k 3 1
  push_cast at hne_f2
  have hne_f3 := x_ne W k 5 1
  push_cast at hne_f3
  have hne_f4 := x_ne W k 7 1
  push_cast at hne_f4
  have hne1 : W.x k ≠ (2 : ℝ) / 10 := by
    have h := x_ne W k 2 0; push_cast at h; intro e; exact h (by linarith)
  have hne2 : W.x k ≠ (4 : ℝ) / 10 := by
    have h := x_ne W k 4 0; push_cast at h; intro e; exact h (by linarith)
  have hne3 : W.x k ≠ (6 : ℝ) / 10 := by
    have h := x_ne W k 6 0; push_cast at h; intro e; exact h (by linarith)
  have hne4 : W.x k ≠ (8 : ℝ) / 10 := by
    have h := x_ne W k 8 0; push_cast at h; intro e; exact h (by linarith)
  constructor
  · intro hnot
    rcases lt_or_gt_of_ne hne1 with c1 | c1
    · rcases lt_or_gt_of_ne hne_f0 with d0 | d0
      · exfalso; exact hnot (Or.inl ⟨by linarith, by linarith⟩)
      · exact Or.inl ⟨by linarith, by linarith⟩
    · rcases lt_or_gt_of_ne hne2 with c2 | c2
      · rcases lt_or_gt_of_ne hne_f1 with d1 | d1
        · exfalso; exact hnot (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
        · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      · rcases lt_or_gt_of_ne hne3 with c3 | c3
        · rcases lt_or_gt_of_ne hne_f2 with d2 | d2
          · exfalso; exact hnot (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩)))
          · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
        · rcases lt_or_gt_of_ne hne4 with c4 | c4
          · rcases lt_or_gt_of_ne hne_f3 with d3 | d3
            · exfalso; exact hnot (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩)))
          · rcases lt_or_gt_of_ne hne_f4 with d4 | d4
            · exfalso; exact hnot (Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩)))
  · intro h1s h0s
    rcases h1s with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases h0s with ⟨a0, b0⟩ | ⟨a0, b0⟩ | ⟨a0, b0⟩ | ⟨a0, b0⟩ | ⟨a0, b0⟩ <;> linarith

-- Part 4: Target predicate, return-time partition, and gap equality for A383427

def P (k : ℕ) : Prop := A003849 k = A383422 k

instance P_dec : DecidablePred P :=
  fun k => inferInstanceAs (Decidable (A003849 k = A383422 k))

theorem P_eq_fin (k : ℕ) (hk : k < 76) : P k ↔ (fibIter 9).getD k 0 = (lucasIter 8).getD k 0 := by
  unfold P
  have hf : (fibIter 9).length = 89 := by decide
  have hl : (lucasIter 8).length = 76 := by decide
  rw [A003849_eq_of_lt 9 k (by omega), A383422_eq_of_lt 8 k (by omega)]

theorem P_iff_reg (W : Wd) (k : ℕ) : P k ↔ ((((0 : ℝ) + (0 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((-1 : ℝ) + (1 : ℝ) * W.s) / 10) ∨ (((2 : ℝ) + (0 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((1 : ℝ) + (1 : ℝ) * W.s) / 10) ∨ (((4 : ℝ) + (0 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((0 : ℝ) + (2 : ℝ) * W.s) / 10) ∨ (((3 : ℝ) + (1 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((6 : ℝ) + (0 : ℝ) * W.s) / 10) ∨ (((5 : ℝ) + (1 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((8 : ℝ) + (0 : ℝ) * W.s) / 10) ∨ (((7 : ℝ) + (1 : ℝ) * W.s) / 10 < W.x k ∧ W.x k < ((10 : ℝ) + (0 : ℝ) * W.s) / 10)) := by
  have hFb := A003849_zero_or_one W k
  have hLb := A383422_zero_or_one W k
  have hP01 : P k ↔ (A003849 k = 0 ∧ A383422 k = 0) ∨ (A003849 k = 1 ∧ A383422 k = 1) := by
    unfold P
    rcases hFb with hF | hF <;> rcases hLb with hL | hL <;> simp [hF, hL]
  rw [hP01, A003849_eq_zero_iff W, A383422_eq_zero_iff W, A003849_eq_one_iff W, A383422_eq_one_iff W]
  constructor
  · rintro (⟨hF, hL⟩ | ⟨hF, hL⟩)
    · rcases hF with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h1, by linarith⟩))
      · linarith [s_lo W, s_hi W]
      · linarith [s_lo W, s_hi W]
    · rcases hF with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith [s_lo W, s_hi W]
      · linarith [s_lo W, s_hi W]
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨Or.inl ⟨h1, h2⟩, by linarith [s_lo W, s_hi W]⟩
    · exact Or.inl ⟨Or.inr (Or.inl ⟨h1, h2⟩), by linarith [s_lo W, s_hi W]⟩
    · exact Or.inl ⟨Or.inr (Or.inr (Or.inl ⟨h1, by linarith [s_lo W, s_hi W]⟩)), by linarith⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)), by linarith [s_lo W, s_hi W]⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))), by linarith [s_lo W, s_hi W]⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))), by linarith [s_lo W, s_hi W]⟩

theorem next_gap (W : Wd) (k : ℕ) (hk : P k) :
    ∃ d ∈ ({1, 2, 3, 5, 6} : Set ℕ), P (k + d) ∧
      ∀ j : ℕ, 0 < j → j < d → j ∉ ({1, 2, 3, 5, 6} : Set ℕ) → ¬ P (k + j) := by
  rw [P_iff_reg W] at hk
  rcases hk with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · 
    have hne0 := x_ne W k (-4) 2
    push_cast at hne0
    rcases lt_or_gt_of_ne hne0 with hlt0 | hgt0
    · 
      refine ⟨1, by simp, ?_, ?_⟩
      · rw [P_iff_reg W]
        have hxd := x_shift W k 1 (0) (by push_cast; linarith [s_lo W, s_hi W]) (by push_cast; linarith [s_lo W, s_hi W])
        push_cast at hxd
        exact Or.inr (Or.inl ⟨by linarith [s_lo W, s_hi W], by linarith [s_lo W, s_hi W]⟩)
      · intro j hj1 hj2 hjG
        exfalso; apply hjG
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
    · 
      have hne1 := x_ne W k (-15) 7
      push_cast at hne1
      rcases lt_or_gt_of_ne hne1 with hlt1 | hgt1
      · 
        refine ⟨5, by simp, ?_, ?_⟩
        · rw [P_iff_reg W]
          have hxd := x_shift W k 5 (1) (by push_cast; linarith [s_lo W, s_hi W]) (by push_cast; linarith [s_lo W, s_hi W])
          push_cast at hxd
          exact Or.inr (Or.inr (Or.inl ⟨by linarith [s_lo W, s_hi W], by linarith [s_lo W, s_hi W]⟩))
        · intro j hj1 hj2 hjG hPj
          have hjcases : j = 4 := by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hjG; omega
          rw [P_iff_reg W] at hPj
          subst hjcases
          have hxj := x_shift W k 4 (1) (by push_cast; linarith [s_lo W, s_hi W]) (by push_cast; linarith [s_lo W, s_hi W])
          push_cast at hxj
          rcases hPj with ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
          · linarith [s_lo W, s_hi W]
          · linarith [s_lo W, s_hi W]
          · linarith [s_lo W, s_hi W]
          · linarith [s_lo W, s_hi W]
          · linarith [s_lo W, s_hi W]
          · linarith [s_lo W, s_hi W]
      · 
        have hne2 := x_ne W k (-8) 4
        push_cast at hne2
        rcases lt_or_gt_of_ne hne2 with hlt2 | hgt2
        · 
          refine ⟨6, by simp, ?_, ?_⟩
          · rw [P_iff_reg W]
            have hxd := x_shift W k 6 (1) (by push_cast; linarith [s_lo W, s_hi W]) (by push_cast; linarith [s_lo W, s_hi W])
            push_cast at hxd
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith [s_lo W, s_hi W], by linarith [s_lo W, s_hi W]⟩))))
          · intro j hj1 hj2 hjG hPj
            have hjcases : j = 4 := by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hjG; omega
            rw [P_iff_reg W] at hPj
            subst hjcases
            have hxj := x_shift W k 4 (1) (by push_cast; linarith [s_lo W, s_hi W]) (by push_cast; linarith [s_lo W, s_hi W])
            push_cast at hxj
            rcases hPj with ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
            · linarith [s_lo W, s_hi W]
            · linarith [s_lo W, s_hi W]
            · linarith [s_lo W, s_hi W]
            · linarith [s_lo W, s_hi W]
            · linarith [s_lo W, s_hi W]
            · linarith [s_lo W, s_hi W]
        · 
          refine ⟨3, by simp, ?_, ?_⟩
          · rw [P_iff_reg W]
            have hxd := x_shift W k 3 (0) (by push_cast; linarith [s_lo W, s_hi W]) (by push_cast; linarith [s_lo W, s_hi W])
            push_cast at hxd
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith [s_lo W, s_hi W], by linarith [s_lo W, s_hi W]⟩)))))
          · intro j hj1 hj2 hjG
            exfalso; apply hjG
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
  · 
    have hne0 := x_ne W k (-2) 2
    push_cast at hne0
    rcases lt_or_gt_of_ne hne0 with hlt0 | hgt0
    · 
      refine ⟨2, by simp, ?_, ?_⟩
      · rw [P_iff_reg W]
        have hxd := x_shift W k 2 (0) (by push_cast; linarith [s_lo W, s_hi W]) (by push_cast; linarith [s_lo W, s_hi W])
        push_cast at hxd
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith [s_lo W, s_hi W], by linarith [s_lo W, s_hi W]⟩))))
      · intro j hj1 hj2 hjG
        exfalso; apply hjG
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
    · 
      refine ⟨1, by simp, ?_, ?_⟩
      · rw [P_iff_reg W]
        have hxd := x_shift W k 1 (0) (by push_cast; linarith [s_lo W, s_hi W]) (by push_cast; linarith [s_lo W, s_hi W])
        push_cast at hxd
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith [s_lo W, s_hi W], by linarith [s_lo W, s_hi W]⟩)))
      · intro j hj1 hj2 hjG
        exfalso; apply hjG
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
  · 
    refine ⟨2, by simp, ?_, ?_⟩
    · rw [P_iff_reg W]
      have hxd := x_shift W k 2 (0) (by push_cast; linarith [s_lo W, s_hi W]) (by push_cast; linarith [s_lo W, s_hi W])
      push_cast at hxd
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith [s_lo W, s_hi W], by linarith [s_lo W, s_hi W]⟩)))))
    · intro j hj1 hj2 hjG
      exfalso; apply hjG
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
  · 
    have hne0 := x_ne W k (-1) 3
    push_cast at hne0
    rcases lt_or_gt_of_ne hne0 with hlt0 | hgt0
    · 
      refine ⟨2, by simp, ?_, ?_⟩
      · rw [P_iff_reg W]
        have hxd := x_shift W k 2 (1) (by push_cast; linarith [s_lo W, s_hi W]) (by push_cast; linarith [s_lo W, s_hi W])
        push_cast at hxd
        exact Or.inl ⟨by linarith [s_lo W, s_hi W], by linarith [s_lo W, s_hi W]⟩
      · intro j hj1 hj2 hjG
        exfalso; apply hjG
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
    · 
      refine ⟨3, by simp, ?_, ?_⟩
      · rw [P_iff_reg W]
        have hxd := x_shift W k 3 (1) (by push_cast; linarith [s_lo W, s_hi W]) (by push_cast; linarith [s_lo W, s_hi W])
        push_cast at hxd
        exact Or.inr (Or.inr (Or.inl ⟨by linarith [s_lo W, s_hi W], by linarith [s_lo W, s_hi W]⟩))
      · intro j hj1 hj2 hjG
        exfalso; apply hjG
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
  · 
    refine ⟨1, by simp, ?_, ?_⟩
    · rw [P_iff_reg W]
      have hxd := x_shift W k 1 (1) (by push_cast; linarith [s_lo W, s_hi W]) (by push_cast; linarith [s_lo W, s_hi W])
      push_cast at hxd
      exact Or.inl ⟨by linarith [s_lo W, s_hi W], by linarith [s_lo W, s_hi W]⟩
    · intro j hj1 hj2 hjG
      exfalso; apply hjG
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
  · 
    refine ⟨1, by simp, ?_, ?_⟩
    · rw [P_iff_reg W]
      have hxd := x_shift W k 1 (1) (by push_cast; linarith [s_lo W, s_hi W]) (by push_cast; linarith [s_lo W, s_hi W])
      push_cast at hxd
      exact Or.inr (Or.inl ⟨by linarith [s_lo W, s_hi W], by linarith [s_lo W, s_hi W]⟩)
    · intro j hj1 hj2 hjG
      exfalso; apply hjG
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega

theorem P_infinite (W : Wd) : (Set.ofPred P).Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro m
  induction m with
  | zero =>
    have hk0 : P 0 := by rw [P_eq_fin 0 (by omega)]; decide
    obtain ⟨d, hdG, hdP, _⟩ := next_gap W 0 hk0
    have hdpos : 0 < d := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdG; omega
    exact ⟨0 + d, hdP, by omega⟩
  | succ m ih =>
    obtain ⟨k, hkP, hkm⟩ := ih
    obtain ⟨d, hdG, hdP, _⟩ := next_gap W k hkP
    have hdpos : 0 < d := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdG; omega
    exact ⟨k + d, hdP, by omega⟩

theorem gap_in_set (W : Wd) (m : ℕ) :
    Nat.nth P (m + 1) - Nat.nth P m ∈ ({1, 2, 3, 5, 6} : Set ℕ) := by
  have hinf := P_infinite W
  have hkP : P (Nat.nth P m) := Nat.nth_mem_of_infinite hinf m
  have hk'P : P (Nat.nth P (m + 1)) := Nat.nth_mem_of_infinite hinf (m + 1)
  have hlt : Nat.nth P m < Nat.nth P (m + 1) := Nat.nth_strictMono hinf (Nat.lt_succ_self m)
  obtain ⟨g, hgG, hkgP, hnone⟩ := next_gap W (Nat.nth P m) hkP
  have hgpos : 0 < g := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgG; omega
  have hle : Nat.nth P (m + 1) ≤ Nat.nth P m + g := by
    obtain ⟨r, hr⟩ : ∃ r, Nat.count P (Nat.nth P m + g) = r := ⟨_, rfl⟩
    have hr' : Nat.nth P r = Nat.nth P m + g := by rw [← hr]; exact Nat.nth_count hkgP
    have hmr : m < r := by
      by_contra hge
      have hmono := (Nat.nth_strictMono hinf).monotone (not_lt.mp hge)
      rw [hr'] at hmono
      omega
    have hmono := (Nat.nth_strictMono hinf).monotone (show m + 1 ≤ r by omega)
    rw [hr'] at hmono
    exact hmono
  rcases lt_or_eq_of_le hle with hlt' | heq'
  · by_contra hnotG
    have hsub : Nat.nth P m + (Nat.nth P (m + 1) - Nat.nth P m) = Nat.nth P (m + 1) := by omega
    exact hnone (Nat.nth P (m + 1) - Nat.nth P m) (by omega) (by omega) hnotG
      (by rw [hsub]; exact hk'P)
  · rw [heq', Nat.add_sub_cancel_left]
    exact hgG

theorem gap_mem_of_witness (W : Wd) (k d : ℕ) (hd : 0 < d) (hk : P k) (hkd : P (k + d))
    (hnone : ∀ j : ℕ, 0 < j → j < d → ¬ P (k + j)) :
    d ∈ {d : ℕ | ∃ n : ℕ, 2 ≤ n ∧ a n - a (n - 1) = d} := by
  show ∃ n : ℕ, 2 ≤ n ∧ a n - a (n - 1) = d
  have hinf := P_infinite W
  obtain ⟨m, hm⟩ : ∃ m, Nat.count P k = m := ⟨_, rfl⟩
  have hk' : Nat.nth P m = k := by rw [← hm]; exact Nat.nth_count hk
  have hP2 : P (Nat.nth P (m + 1)) := Nat.nth_mem_of_infinite hinf (m + 1)
  have hlt : k < Nat.nth P (m + 1) := by
    rw [← hk']; exact Nat.nth_strictMono hinf (Nat.lt_succ_self m)
  have hle : Nat.nth P (m + 1) ≤ k + d := by
    obtain ⟨r, hr⟩ : ∃ r, Nat.count P (k + d) = r := ⟨_, rfl⟩
    have hr' : Nat.nth P r = k + d := by rw [← hr]; exact Nat.nth_count hkd
    have hmr : m < r := by
      by_contra hge
      have hmono := (Nat.nth_strictMono hinf).monotone (not_lt.mp hge)
      rw [hr', hk'] at hmono
      omega
    have hmono := (Nat.nth_strictMono hinf).monotone (show m + 1 ≤ r by omega)
    rw [hr'] at hmono
    exact hmono
  have heq : Nat.nth P (m + 1) = k + d := by
    by_contra hne
    have hlt' : Nat.nth P (m + 1) < k + d := lt_of_le_of_ne hle hne
    have hsub : k + (Nat.nth P (m + 1) - k) = Nat.nth P (m + 1) := by omega
    exact hnone (Nat.nth P (m + 1) - k) (by omega) (by omega) (by rw [hsub]; exact hP2)
  refine ⟨m + 2, by omega, ?_⟩
  have ha1 : a (m + 2 - 1) = k := by
    show Nat.nth P (m + 2 - 1 - 1) = k
    rw [show m + 2 - 1 - 1 = m by omega]
    exact hk'
  have ha2 : a (m + 2) = Nat.nth P (m + 1) := by
    show Nat.nth P (m + 2 - 1) = Nat.nth P (m + 1)
    rw [show m + 2 - 1 = m + 1 by omega]
  rw [ha2, heq, ha1]
  omega

end ProofA383427

open OMA.S_oeis_a383427 ProofA383427 in
theorem OMA.solution : type_of% @OMA.S_oeis_a383427.main := by
  obtain ⟨W⟩ := Wd_nonempty
  ext d
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have ha1 : a (m + 2 - 1) = Nat.nth P m := by
      show Nat.nth P (m + 2 - 1 - 1) = Nat.nth P m
      rw [show m + 2 - 1 - 1 = m by omega]
    have ha2 : a (m + 2) = Nat.nth P (m + 1) := by
      show Nat.nth P (m + 2 - 1) = Nat.nth P (m + 1)
      rw [show m + 2 - 1 = m + 1 by omega]
    rw [ha2, ha1]
    exact gap_in_set W m
  · intro hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · refine gap_mem_of_witness W 0 1 (by omega) ?_ ?_ ?_
      · rw [P_eq_fin 0 (by omega)]; decide
      · rw [P_eq_fin (0 + 1) (by omega)]; decide
      · intro j hj1 hj2; omega
    · refine gap_mem_of_witness W 1 2 (by omega) ?_ ?_ ?_
      · rw [P_eq_fin 1 (by omega)]; decide
      · rw [P_eq_fin (1 + 2) (by omega)]; decide
      · intro j hj1 hj2
        have hj : j = 1 := by omega
        subst hj; rw [P_eq_fin (1 + 1) (by omega)]; decide
    · refine gap_mem_of_witness W 3 3 (by omega) ?_ ?_ ?_
      · rw [P_eq_fin 3 (by omega)]; decide
      · rw [P_eq_fin (3 + 3) (by omega)]; decide
      · intro j hj1 hj2
        have hj : j = 1 ∨ j = 2 := by omega
        rcases hj with rfl | rfl
        · rw [P_eq_fin (3 + 1) (by omega)]; decide
        · rw [P_eq_fin (3 + 2) (by omega)]; decide
    · refine gap_mem_of_witness W 39 5 (by omega) ?_ ?_ ?_
      · rw [P_eq_fin 39 (by omega)]; decide
      · rw [P_eq_fin (39 + 5) (by omega)]; decide
      · intro j hj1 hj2
        have hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
        rcases hj with rfl | rfl | rfl | rfl
        · rw [P_eq_fin (39 + 1) (by omega)]; decide
        · rw [P_eq_fin (39 + 2) (by omega)]; decide
        · rw [P_eq_fin (39 + 3) (by omega)]; decide
        · rw [P_eq_fin (39 + 4) (by omega)]; decide
    · refine gap_mem_of_witness W 21 6 (by omega) ?_ ?_ ?_
      · rw [P_eq_fin 21 (by omega)]; decide
      · rw [P_eq_fin (21 + 6) (by omega)]; decide
      · intro j hj1 hj2
        have hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
        rcases hj with rfl | rfl | rfl | rfl | rfl
        · rw [P_eq_fin (21 + 1) (by omega)]; decide
        · rw [P_eq_fin (21 + 2) (by omega)]; decide
        · rw [P_eq_fin (21 + 3) (by omega)]; decide
        · rw [P_eq_fin (21 + 4) (by omega)]; decide
        · rw [P_eq_fin (21 + 5) (by omega)]; decide
