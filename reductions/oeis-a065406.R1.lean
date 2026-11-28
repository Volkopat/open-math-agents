import OMAStatements.S_oeis_a065406

/-! Use the supplementary law for two to exclude Mersenne exponents three modulo four. -/

namespace OMA.R_oeis_a065406_R1

open OMA.S_oeis_a065406

def H1 : Prop := {p : ℕ | IsTerm p ∧ p % 24 = 5}.Finite
def H2 : Prop := {p : ℕ | IsTerm p ∧ p % 24 = 17}.Finite

lemma growth (p : ℕ) (hp : 4 ≤ p) : 2*p+2 < 2^p := by
  induction p,hp using Nat.le_induction with
  | base => decide
  | succ n hn ih => rw [pow_succ]; omega

lemma excludes_three_mod_four {p : ℕ} (hp : 3 < p) (h : IsTerm p) : p%4 ≠ 3 := by
  intro hr
  obtain ⟨_,hM,hq⟩ := h
  let q := 2*p+1
  letI : Fact q.Prime := ⟨hq⟩
  have h8 : q%8 = 7 := by dsimp [q]; omega
  have hsym : legendreSym q 2 = 1 := by
    rw [legendreSym.at_two (by omega), ZMod.χ₈_nat_eq_if_mod_eight]
    omega
  have he := legendreSym.eq_pow q (2 : ℤ)
  rw [hsym,show q/2=p by dsimp [q]; omega] at he
  have hpow : (2 : ZMod q)^p = 1 := by simpa using he.symm
  have hpos : 1 ≤ (2:ℕ)^p := Nat.one_le_two_pow
  have hd : q ∣ 2^p-1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast [Nat.cast_sub hpos]
    rw [hpow]
    simp
  have heq := (Nat.dvd_prime_two_le hM (by dsimp [q]; omega : 2 ≤ q)).mp hd
  have hg := growth p (by omega)
  dsimp [q] at heq
  omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a065406.main := by
  intro h1 h2
  apply (((Set.finite_Iic 3).union h1).union h2).subset
  intro p hp
  change (p ≤ 3 ∨ IsTerm p ∧ p%24=5) ∨ IsTerm p ∧ p%24=17
  by_cases small : p ≤ 3
  · exact Or.inl (Or.inl small)
  have hx := excludes_three_mod_four (by omega) hp
  obtain ⟨hP,_,hq⟩ := (show IsTerm p from hp)
  have hodd := hP.eq_two_or_odd.resolve_left (by omega)
  have hn3 : p%3 ≠ 0 := by
    intro hz
    have he := (Nat.dvd_prime_two_le hP (by decide : 2 ≤ 3)).mp (Nat.dvd_of_mod_eq_zero hz)
    omega
  have hn1 : p%3 ≠ 1 := by
    intro hz
    have hd : 3 ∣ 2*p+1 := Nat.dvd_of_mod_eq_zero (by omega)
    have he := (Nat.dvd_prime_two_le hq (by decide : 2 ≤ 3)).mp hd
    omega
  rcases (show p%24 = 5 ∨ p%24 = 17 by omega) with h | h
  · exact Or.inl (Or.inr ⟨hp,h⟩)
  · exact Or.inr ⟨hp,h⟩

end OMA.R_oeis_a065406_R1
