import OMAStatements.S_oeis_a294200

/-!
The shifted-prime theorem of Guo and Weingartner supplies H1 (Integers 18,
2018, A93, Proposition 1, shift 1). Their B₀ numbers admit the displayed
factor list by writing down the prime factors in increasing order with
repetitions. H2 transfers this condition to practical shifted powers of two.
Credit: @krgrocon
-/
namespace OMA.R_oeis_a294200_R1

def H1 : Prop := {p : ℕ | p.Prime ∧ ∃ l : List ℕ, l.prod = p-1 ∧
  ∀ i : Fin l.length, l[i].Prime ∧ l[i] ≤ max 2 (l.take i.val).prod}.Infinite

def H2 : Prop := ∀ l : List ℕ,
  (∀ i : Fin l.length, l[i].Prime ∧ l[i] ≤ max 2 (l.take i.val).prod) →
    OMA.S_oeis_a294200.IsPractical (2*(2^l.prod-1))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a294200.main := by
  intro h1 h2
  apply h1.mono
  intro p ⟨hpp, l, he, hfactor⟩
  refine ⟨hpp, ?_⟩
  have hp := h2 l hfactor
  rw [he] at hp
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpp.ne_zero
  simp only [Nat.succ_sub_one] at hp
  rw [pow_succ]
  have hv : 0 < (2:ℕ)^t := pow_pos (by decide) _
  convert hp using 1 <;> omega

end OMA.R_oeis_a294200_R1
