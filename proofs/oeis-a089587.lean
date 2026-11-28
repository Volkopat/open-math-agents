import OMAStatements.S_oeis_a089587

/-!
For the fifth Fermat number, powers of base 2 have 32 descents in a
period of 64. The unit 2787373473 has three descents in a period of five.
It can be found by taking an element of order five modulo 641 and lifting
it to be 1 modulo 6700417. Only the two short periods are evaluated here.
-/

namespace FermatDescents

open Finset OMA.S_oeis_a089587

private def modulus : ℕ := 4294967297
private def base : ℕ := 2787373473

private def descent (k i : ℕ) : ℕ :=
  if k^(i+2) % modulus < k^(i+1) % modulus then 1 else 0

private theorem count_eq (k : ℕ) :
    descCount modulus k = ∑ i ∈ range 4294967296, descent k i := by
  unfold descCount
  rw [Finset.card_filter, show Icc 1 (modulus-1) = Ico 1 modulus by
    ext i; simp only [mem_Icc, mem_Ico]; dsimp [modulus]; omega, Finset.sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro i _
  simp only [descent, Nat.add_comm 1 i, Nat.add_assoc]

private theorem periodic {k d : ℕ} (hd : k^d % modulus = 1) (i : ℕ) :
    descent k (i+d) = descent k i := by
  have red (j : ℕ) : k^(j+d) % modulus = k^j % modulus := by
    rw [pow_add, Nat.mul_mod, hd, mul_one, Nat.mod_mod]
  simp only [descent, show i+d+2 = (i+2)+d by omega, show i+d+1 = (i+1)+d by omega, red]

private theorem blocks (f : ℕ → ℕ) (d b r : ℕ) (per : ∀ i, f (i+d)=f i) :
    ∑ i ∈ range (b*d+r), f i = b*(∑ i ∈ range d, f i) + ∑ i ∈ range r, f i := by
  have shift (t i : ℕ) : f (t*d+i) = f i := by
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.succ_mul, show t*d+d+i = (t*d+i)+d by omega, per, ih]
  have full (t : ℕ) : ∑ i ∈ range (t*d), f i = t*(∑ i ∈ range d, f i) := by
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.succ_mul, sum_range_add, ih, Nat.succ_mul]; simp only [shift]
  rw [sum_range_add, full]
  simp only [shift]

theorem count_two : descCount modulus 2 = 2147483648 := by
  have c : ∑ i ∈ range 64, descent 2 i = 32 := by decide
  have p := blocks (descent 2) 64 67108864 0 (periodic (by decide))
  rw [count_eq, show 4294967296 = 67108864*64+0 by decide, p, c]
  decide

theorem count_competitor : descCount modulus base = 2576980378 := by
  have c : ∑ i ∈ range 5, descent base i = 3 := by decide
  have d : ∑ i ∈ range 1, descent base i = 1 := by decide
  have p := blocks (descent base) 5 858993459 1 (periodic (by decide))
  rw [count_eq, show 4294967296 = 858993459*5+1 by decide, p, c, d]

theorem two_fails : a modulus ≠ 2 := by
  intro wrong
  let S := {k : ℕ | 0 < k ∧ k < modulus ∧ ∀ j : ℕ, 0 < j → j < modulus →
    descCount modulus j ≤ descCount modulus k}
  change sInf S = 2 at wrong
  have ne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr (by
    intro empty
    simp [empty] at wrong)
  have best := Nat.sInf_mem ne
  rw [wrong] at best
  have cmp := best.2.2 base (by decide) (by decide)
  rw [count_two, count_competitor] at cmp
  omega

end FermatDescents

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a089587.main) := by
  intro h
  exact FermatDescents.two_fails ((h.1 _ (by decide)).mpr ⟨5, by decide⟩)
