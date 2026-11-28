import OMAStatements.S_oeis_a288736

-- Problem: A288736: 2-limiting word of the mapping 00->1000, 10->01, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a288736.lean:0 (declaration OMA.S_oeis_a288736.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let B(m) = (110)^m and the segments S0(m) = B(m) 00, S1(m) = 10 S0(m),
-- S2(m) = 0 S0(m+1), S3(m) = 0 S1(m+1). Whatever word r follows, step(S0(m) r) = S1(m) step(r),
-- step(S1(m) r) = S2(m) step(r), step(S2(m) r) = S3(m) step(r) and
-- step(S3(m) r) = S0(0) S0(m+2) step(r). So w(4k) is a concatenation of 2^k segments S0(m), each
-- step adds 2 letters per segment, and the length grows by 2*2^(n/4) from w(n) to w(n+1). That
-- gives L(n+5) - L(n+4) = 2*(L(n+1) - L(n)), the recurrence of A288732, with the same first
-- five values 2, 4, 6, 8, 10.

namespace P1A288736

open OMA.S_oeis_a288736

theorem step_00 (r : List Bool) :
    step (false :: false :: r) = true :: false :: false :: false :: step r := rfl

theorem step_10 (r : List Bool) : step (true :: false :: r) = false :: true :: step r := rfl

theorem step_11 (r : List Bool) : step (true :: true :: r) = true :: step (true :: r) := rfl

theorem step_01 (r : List Bool) : step (false :: true :: r) = false :: step (true :: r) := rfl

/-- (110)^m. -/
def blk : ℕ → List Bool
  | 0 => []
  | m + 1 => true :: true :: false :: blk m

def S0 (m : ℕ) : List Bool := blk m ++ [false, false]

def S1 (m : ℕ) : List Bool := true :: false :: S0 m

def S2 (m : ℕ) : List Bool := false :: S0 (m + 1)

def S3 (m : ℕ) : List Bool := false :: S1 (m + 1)

theorem key : ∀ (m : ℕ) (r : List Bool), step (S0 m ++ r) = S1 m ++ step r
  | 0, r => by
    show step (false :: false :: r) = true :: false :: false :: false :: step r
    exact step_00 r
  | m + 1, r => by
    show step (true :: true :: false :: (S0 m ++ r)) = true :: false :: true :: (S1 m ++ step r)
    rw [step_11, step_10, key m r]

theorem seg1 (m : ℕ) (r : List Bool) : step (S1 m ++ r) = S2 m ++ step r := by
  show step (true :: false :: (S0 m ++ r)) = false :: true :: (S1 m ++ step r)
  rw [step_10, key]

theorem seg2 (m : ℕ) (r : List Bool) : step (S2 m ++ r) = S3 m ++ step r := by
  show step (false :: true :: true :: false :: (S0 m ++ r)) =
    false :: true :: false :: true :: (S1 m ++ step r)
  rw [step_01, step_11, step_10, key]

theorem seg3 (m : ℕ) (r : List Bool) :
    step (S3 m ++ r) = S0 0 ++ (S0 (m + 2) ++ step r) := by
  show step (false :: true :: false :: true :: true :: false :: (S0 m ++ r)) =
    false :: false :: true :: true :: false :: true :: (S1 m ++ step r)
  rw [step_01, step_10, step_11, step_10, key]

def W0 : List ℕ → List Bool
  | [] => []
  | m :: L => S0 m ++ W0 L

def W1 : List ℕ → List Bool
  | [] => []
  | m :: L => S1 m ++ W1 L

def W2 : List ℕ → List Bool
  | [] => []
  | m :: L => S2 m ++ W2 L

def W3 : List ℕ → List Bool
  | [] => []
  | m :: L => S3 m ++ W3 L

def dbl : List ℕ → List ℕ
  | [] => []
  | m :: L => 0 :: (m + 2) :: dbl L

theorem stepW0 : ∀ L : List ℕ, step (W0 L) = W1 L
  | [] => rfl
  | m :: L => by
    show step (S0 m ++ W0 L) = S1 m ++ W1 L
    rw [key, stepW0 L]

theorem stepW1 : ∀ L : List ℕ, step (W1 L) = W2 L
  | [] => rfl
  | m :: L => by
    show step (S1 m ++ W1 L) = S2 m ++ W2 L
    rw [seg1, stepW1 L]

theorem stepW2 : ∀ L : List ℕ, step (W2 L) = W3 L
  | [] => rfl
  | m :: L => by
    show step (S2 m ++ W2 L) = S3 m ++ W3 L
    rw [seg2, stepW2 L]

theorem stepW3 : ∀ L : List ℕ, step (W3 L) = W0 (dbl L)
  | [] => rfl
  | m :: L => by
    show step (S3 m ++ W3 L) = S0 0 ++ (S0 (m + 2) ++ W0 (dbl L))
    rw [seg3, stepW3 L]

theorem len_blk : ∀ m : ℕ, (blk m).length = 3 * m
  | 0 => rfl
  | m + 1 => by
    have h := len_blk m
    show (blk m).length + 1 + 1 + 1 = 3 * (m + 1)
    omega

theorem len_S0 (m : ℕ) : (S0 m).length = 3 * m + 2 := by
  have h := len_blk m
  show (blk m ++ [false, false]).length = 3 * m + 2
  rw [List.length_append]
  show (blk m).length + 2 = 3 * m + 2
  omega

theorem len_S1 (m : ℕ) : (S1 m).length = 3 * m + 4 := by
  have h := len_S0 m
  show (S0 m).length + 1 + 1 = 3 * m + 4
  omega

theorem len_S2 (m : ℕ) : (S2 m).length = 3 * m + 6 := by
  have h := len_S0 (m + 1)
  show (S0 (m + 1)).length + 1 = 3 * m + 6
  omega

theorem len_S3 (m : ℕ) : (S3 m).length = 3 * m + 8 := by
  have h := len_S1 (m + 1)
  show (S1 (m + 1)).length + 1 = 3 * m + 8
  omega

theorem lenW01 : ∀ L : List ℕ, (W1 L).length = (W0 L).length + 2 * L.length
  | [] => rfl
  | m :: L => by
    have h0 := len_S0 m
    have h1 := len_S1 m
    have ih := lenW01 L
    show (S1 m ++ W1 L).length = (S0 m ++ W0 L).length + 2 * (L.length + 1)
    rw [List.length_append, List.length_append]
    omega

theorem lenW12 : ∀ L : List ℕ, (W2 L).length = (W1 L).length + 2 * L.length
  | [] => rfl
  | m :: L => by
    have h1 := len_S1 m
    have h2 := len_S2 m
    have ih := lenW12 L
    show (S2 m ++ W2 L).length = (S1 m ++ W1 L).length + 2 * (L.length + 1)
    rw [List.length_append, List.length_append]
    omega

theorem lenW23 : ∀ L : List ℕ, (W3 L).length = (W2 L).length + 2 * L.length
  | [] => rfl
  | m :: L => by
    have h2 := len_S2 m
    have h3 := len_S3 m
    have ih := lenW23 L
    show (S3 m ++ W3 L).length = (S2 m ++ W2 L).length + 2 * (L.length + 1)
    rw [List.length_append, List.length_append]
    omega

theorem lenW30 : ∀ L : List ℕ, (W0 (dbl L)).length = (W3 L).length + 2 * L.length
  | [] => rfl
  | m :: L => by
    have h0 := len_S0 0
    have h2 := len_S0 (m + 2)
    have h3 := len_S3 m
    have ih := lenW30 L
    show (S0 0 ++ (S0 (m + 2) ++ W0 (dbl L))).length =
      (S3 m ++ W3 L).length + 2 * (L.length + 1)
    rw [List.length_append, List.length_append, List.length_append]
    omega

theorem len_dbl : ∀ L : List ℕ, (dbl L).length = 2 * L.length
  | [] => rfl
  | m :: L => by
    have ih := len_dbl L
    show (dbl L).length + 1 + 1 = 2 * (L.length + 1)
    omega

theorem inv : ∀ k : ℕ, ∃ L : List ℕ, L.length = 2 ^ k ∧ w (4 * k) = W0 L
  | 0 => ⟨[0], rfl, rfl⟩
  | k + 1 => by
    obtain ⟨L, hL, hw⟩ := inv k
    refine ⟨dbl L, ?_, ?_⟩
    · rw [len_dbl, hL]
      ring
    · have e : 4 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 := by ring
      rw [e]
      show step (step (step (step (w (4 * k))))) = W0 (dbl L)
      rw [hw, stepW0, stepW1, stepW2, stepW3]

theorem incr (k : ℕ) :
    (w (4 * k + 1)).length = (w (4 * k)).length + 2 * 2 ^ k ∧
    (w (4 * k + 2)).length = (w (4 * k + 1)).length + 2 * 2 ^ k ∧
    (w (4 * k + 3)).length = (w (4 * k + 2)).length + 2 * 2 ^ k ∧
    (w (4 * k + 4)).length = (w (4 * k + 3)).length + 2 * 2 ^ k := by
  obtain ⟨L, hL, hw⟩ := inv k
  have e1 : w (4 * k + 1) = W1 L := by
    show step (w (4 * k)) = W1 L
    rw [hw, stepW0]
  have e2 : w (4 * k + 2) = W2 L := by
    show step (w (4 * k + 1)) = W2 L
    rw [e1, stepW1]
  have e3 : w (4 * k + 3) = W3 L := by
    show step (w (4 * k + 2)) = W3 L
    rw [e2, stepW2]
  have e4 : w (4 * k + 4) = W0 (dbl L) := by
    show step (w (4 * k + 3)) = W0 (dbl L)
    rw [e3, stepW3]
  have l1 := lenW01 L
  have l2 := lenW12 L
  have l3 := lenW23 L
  have l4 := lenW30 L
  rw [hL] at l1 l2 l3 l4
  rw [e1, e2, e3, e4, hw]
  omega

theorem dstepN (j : ℕ) : (w (j + 1)).length = (w j).length + 2 * 2 ^ (j / 4) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r < 4 ∧ j = 4 * q + r :=
    ⟨j / 4, j % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 4).symm⟩
  have hq : (4 * q + r) / 4 = q := by omega
  rw [hq]
  obtain ⟨i1, i2, i3, i4⟩ := incr q
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with h | h | h | h
  · subst h
    exact i1
  · subst h
    exact i2
  · subst h
    exact i3
  · subst h
    exact i4

theorem len_eq : ∀ n : ℕ,
    ((w n).length : ℤ) = A288732 n ∧ ((w (n + 1)).length : ℤ) = A288732 (n + 1) ∧
    ((w (n + 2)).length : ℤ) = A288732 (n + 2) ∧ ((w (n + 3)).length : ℤ) = A288732 (n + 3) ∧
    ((w (n + 4)).length : ℤ) = A288732 (n + 4)
  | 0 => ⟨by decide, by decide, by decide, by decide, by decide⟩
  | n + 1 => by
    obtain ⟨h0, h1, h2, h3, h4⟩ := len_eq n
    refine ⟨h1, h2, h3, h4, ?_⟩
    show ((w (n + 5)).length : ℤ) = A288732 (n + 5)
    have hd4 : (w (n + 5)).length = (w (n + 4)).length + 2 * 2 ^ ((n + 4) / 4) := dstepN (n + 4)
    have hd0 : (w (n + 1)).length = (w n).length + 2 * 2 ^ (n / 4) := dstepN n
    have hq : (n + 4) / 4 = n / 4 + 1 := by omega
    rw [hq, pow_succ] at hd4
    have hkey : (w (n + 5)).length + 2 * (w n).length =
        (w (n + 4)).length + 2 * (w (n + 1)).length := by omega
    have hkey' : ((w (n + 5)).length : ℤ) + 2 * ((w n).length : ℤ) =
        ((w (n + 4)).length : ℤ) + 2 * ((w (n + 1)).length : ℤ) := by exact_mod_cast hkey
    have hA : A288732 (n + 5) = A288732 (n + 4) + 2 * A288732 (n + 1) - 2 * A288732 n := rfl
    rw [hA, ← h4, ← h1, ← h0]
    linarith

end P1A288736

open OMA.S_oeis_a288736 P1A288736 in
theorem OMA.solution : type_of% @OMA.S_oeis_a288736.main := by
  intro n
  exact (len_eq n).1
