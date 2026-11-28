import OMAStatements.S_oeis_a007228
import Mathlib

namespace OMA.BinomialParity7228

open OMA.S_oeis_a007228

private theorem halve (n k : ℕ) : (2*n).choose k % 2 =
    if k%2 = 0 then n.choose (k/2) % 2 else 0 := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := 2*n) (k := k)
  change _ % 2 = _ % 2 at h
  by_cases e : k%2 = 0
  · simpa [e, Nat.mul_comm] using h
  · have o : k%2 = 1 := by omega
    simpa [e,o,Nat.mul_comm] using h

private theorem quarters (n k : ℕ) : (4*n).choose k % 2 =
    if k%4 = 0 then n.choose (k/4) % 2 else 0 := by
  rw [show 4*n = 2*(2*n) by omega, halve, halve]
  have q : k/2/2 = k/4 := by omega
  rw [q]
  split_ifs <;> omega

private theorem even_central (n : ℕ) (hn : 0 < n) : (4*n).choose n % 2 = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [quarters]
    split_ifs with e
    · have h := ih (n/4) (by omega) (by omega)
      have eq : 4*(n/4) = n := by omega
      rwa [eq] at h
    · rfl

private theorem parity (n : ℕ) (hn : 0 < n) : a n % 2 = (4*n).choose (n+1) % 2 := by
  let c := (4*n).choose n
  let d := (4*n).choose (n+1)
  have h : d*(n+1) = c*(3*n) := by
    simpa [c,d,show 4*n-n = 3*n by omega] using Nat.choose_succ_right_eq (4*n) n
  have eq : 3*c + d*(n+1) = (3*c)*(n+1) := by rw [h]; ring
  have divided := congrArg (fun x : ℕ => x/(n+1)) eq
  have den : 0 < n+1 := by omega
  simp only [Nat.add_mul_div_right _ _ den, Nat.mul_div_cancel _ den] at divided
  have he : c%2 = 0 := even_central n hn
  change (3*c/(n+1))%2 = d%2
  omega

private theorem adjacent (m : ℕ) :
    (4*m+3).choose (m+1) = 3*(4*m+3).choose m := by
  apply Nat.eq_of_mul_eq_mul_right (show 0 < m+1 by omega)
  rw [Nat.choose_succ_right_eq, show 4*m+3-m = 3*(m+1) by omega]
  ring

theorem result (n : ℕ) (hn : 1 ≤ n) : a n % 2 = 1 ↔
    ∃ m : ℕ, n = 4*m+3 ∧ (4*m+3).choose m % 2 = 1 := by
  rw [parity n hn,quarters]
  constructor
  · intro h
    split_ifs at h with e
    · let m := n/4
      have eq : n = 4*m+3 := by dsimp [m]; omega
      have q : (n+1)/4 = m+1 := by omega
      rw [q,eq,adjacent] at h
      exact ⟨m,eq,by omega⟩
  · rintro ⟨m,rfl,h⟩
    rw [if_pos (show (4*m+3+1)%4=0 by omega),
      show (4*m+3+1)/4=m+1 by omega, adjacent]
    omega

end OMA.BinomialParity7228

theorem OMA.solution : type_of% @OMA.S_oeis_a007228.main := OMA.BinomialParity7228.result
