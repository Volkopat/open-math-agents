import OMAStatements.S_oeis_a355898

/-!
Tom Adamczewski, *OEIS Open*, Appendix A, gives the modulus and indices
used here for Giorgos Kalogeropoulos's conjecture on OEIS A355898.
-/

open OMA.S_oeis_a355898

private abbrev P := 195318521017
private abbrev R := ZMod P

/-- The two entries are consecutive Fibonacci residues. -/
private def residues (n : ℕ) : R × R :=
  if _h : n = 0 then (0, 1)
  else
    let (u, v) := residues (n / 2)
    let c := u * (2*v-u)
    let d := v^2 + u^2
    if n % 2 = 0 then (c,d) else (d,c+d)
termination_by n
decreasing_by omega

private theorem residues_eq (n : ℕ) :
    residues n = ((Nat.fib n : R), (Nat.fib (n+1) : R)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [residues]
    split
    · rename_i h
      subst n
      simp
    · rename_i h
      let k := n / 2
      have hk : k < n := by dsimp [k]; omega
      rw [ih _ hk]
      change (if n % 2 = 0 then _ else _) = _
      have hle : Nat.fib k ≤ 2 * Nat.fib (k+1) := by
        have := Nat.fib_le_fib_succ (n := k)
        omega
      have hd : (Nat.fib (2*k) : R) =
          (Nat.fib k : R) * (2*(Nat.fib (k+1) : R) - Nat.fib k) := by
        rw [Nat.fib_two_mul, Nat.cast_mul, Nat.cast_sub hle]
        push_cast
        rfl
      have he : (Nat.fib (2*k+1) : R) = (Nat.fib (k+1) : R)^2 + (Nat.fib k : R)^2 := by
        rw [Nat.fib_two_mul_add_one]; push_cast; rfl
      split_ifs with heven
      · have hn : n = 2*k := by dsimp [k]; omega
        conv_rhs => rw [hn]
        exact Prod.ext hd.symm he.symm
      · have hn : n = 2*k+1 := by dsimp [k]; omega
        conv_rhs => rw [hn]
        apply Prod.ext he.symm
        change _ = (Nat.fib (2*k+2) : R)
        rw [Nat.fib_add_two, Nat.cast_add, hd, he]

private theorem a_rec (n : ℕ) : a (n+3) = nextTerm (a (n+1)) (a (n+2)) := rfl

private theorem impossible {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hpx : P ∣ x) (hpy : P ∣ y) : nextTerm x y ≠ 1 + x + y := by
  let g := Nat.gcd x y
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hx
  have hp : P ≤ g := Nat.le_of_dvd hg (Nat.dvd_gcd hpx hpy)
  have gx : g ≤ x := Nat.le_of_dvd hx (Nat.gcd_dvd_left x y)
  have gy : g ≤ y := Nat.le_of_dvd hy (Nat.gcd_dvd_right x y)
  have two : 2 ≤ P := by decide
  have hdiv : (x+y)/g ≤ (x+y)/2 := Nat.div_le_div_left (by omega) (by decide)
  change g + (x+y)/g ≠ 1+x+y
  omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem seed : a 3772 % P = 21827756562 ∧ a 3774 % P = 99768150821 := by
  decide +kernel

private def predicted (n : ℕ) : R :=
  (((99768150821 : ℕ) : R) + 1) * (residues (n-3772)).1 - (((21827756562 : ℕ) : R) + 1) * (residues (n-3774)).1 - 1

private theorem collision {n : ℕ} (h : (a n : ℤ) = fibFormula n) (hz : predicted n = 0) :
    P ∣ a n := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  have eq := congrArg (fun z : ℤ => (z : R)) h
  simp only [fibFormula, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_one,
    Int.cast_natCast] at eq
  rw [eq, ← ZMod.natCast_mod (a 3772) P, ← ZMod.natCast_mod (a 3774) P, seed.1, seed.2]
  simpa only [predicted, residues_eq] using hz

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a355898.main) := by
  intro h
  let n := 249580077006
  have hx := h n (by decide)
  have hy := h (n+1) (by decide)
  have hz := (h (n+2) (by decide)).1
  have px := collision hx.2.2 (by decide +kernel)
  have py := collision hy.2.2 (by decide +kernel)
  have rec' : a (n+2) = nextTerm (a n) (a (n+1)) := a_rec (n-1)
  exact impossible (by omega : 0 < a n) (by omega : 0 < a (n+1)) px py
    (rec'.symm.trans (by simpa only [show n+2-1 = n+1 by omega, show n+2-2 = n by omega,
      Nat.add_right_comm] using hz))
