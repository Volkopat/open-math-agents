import OMAStatements.S_oeis_a002145
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace OMA.R_oeis_a002145_R2

open OMA.S_oeis_a002145

/-- A lower bound on the number of eligible first primes up to half the input. -/
def H1 : Prop :=
  ∀ x : ℕ, 132 ≤ x →
    x / (8 * (x.log2 + 1)) <
      ((Finset.range (x / 2 + 1)).filter (fun q => q.Prime ∧ q % 4 = 1)).card

/-- An upper bound on the number of exceptions to the binary problem from 66 to x. -/
def H2 : Prop :=
  ∀ x : ℕ, 132 ≤ x →
    ((Finset.Icc 66 x).filter (fun e => e % 4 = 2 ∧
      ∀ r ∈ Finset.range (e + 1), r.Prime → r % 4 = 1 → ¬ (e-r).Prime)).card ≤
      x / (8 * (x.log2 + 1))

lemma small_case {p : ℕ} (hp : p % 4 = 3) (hl : 23 ≤ p) (hu : p < 132) :
    SumOfThreePrimesOneModFour p := by
  let choices : Fin 4 → ℕ := ![5, 13, 17, 29]
  have good : ∀ i, (choices i).Prime ∧ choices i % 4 = 1 := by decide +kernel
  have table : ∀ k : Fin 33, 5 ≤ k.val → ∃ i j : Fin 4,
      (4 * k.val + 3 - (choices i + choices j)).Prime := by decide +kernel
  let k : Fin 33 := ⟨p/4, by omega⟩
  have hk : 4 * k.val + 3 = p := by dsimp [k]; omega
  obtain ⟨i, j, hs⟩ := table k (by dsimp [k]; omega)
  rw [hk] at hs
  have hspos := hs.two_le
  have hi := (good i).2
  have hj := (good j).2
  exact ⟨_, _, _, (good i).1, (good j).1, hs, hi, hj, by omega, by omega⟩

lemma of_counts (lower : H1) (upper : H2) {p : ℕ} (hp : p % 4 = 3) (hlarge : 132 ≤ p) :
    SumOfThreePrimesOneModFour p := by
  let first := (Finset.range (p / 2 + 1)).filter (fun q => q.Prime ∧ q % 4 = 1)
  let bad := (Finset.Icc 66 p).filter (fun e => e % 4 = 2 ∧
    ∀ r ∈ Finset.range (e + 1), r.Prime → r % 4 = 1 → ¬ (e-r).Prime)
  have strict : bad.card < first.card := lt_of_le_of_lt (upper p hlarge) (lower p hlarge)
  by_contra h
  apply (not_le_of_gt strict)
  apply Finset.card_le_card_of_injOn (fun q => p-q)
  · intro q hq
    change p - q ∈ bad
    obtain ⟨hbound, hprime, hmod⟩ := Finset.mem_filter.mp hq
    have hqle := Finset.mem_range.mp hbound
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega, ?_⟩
    intro r hr hrprime hrmod hs
    have hrle := Finset.mem_range.mp hr
    exact h ⟨q, r, p-q-r, hprime, hrprime, hs, hmod, hrmod, by omega, by omega⟩
  · intro a ha b hb h
    have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    change p-a = p-b at h
    omega

-- The zero-based index conversion also appears in reduction R1, PR 32236.
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a002145.main := by
  intro lower upper n hn
  let P : ℕ → Prop := fun p => p.Prime ∧ p % 4 = 3
  have hInf : (Set.ofPred P).Infinite := by
    simpa [P, Set.ofPred, Nat.ModEq] using
      (Nat.infinite_setOfPred_prime_and_modEq (q := 4) (a := 3) (by decide) (by decide))
  let p := Nat.nth P n
  have hp : p.Prime ∧ p % 4 = 3 := Nat.nth_mem_of_infinite hInf n
  have hCount : Nat.count (fun p => p.Prime ∧ p % 4 = 3) 23 = 4 := by decide +kernel
  have hl : 23 ≤ p := (Nat.count_le_iff_le_nth hInf).mp (by simpa [P, hCount] using hn)
  change SumOfThreePrimesOneModFour p
  by_cases hu : p < 132
  · exact small_case hp.2 hl hu
  · exact of_counts lower upper hp.2 (by omega)

end OMA.R_oeis_a002145_R2
