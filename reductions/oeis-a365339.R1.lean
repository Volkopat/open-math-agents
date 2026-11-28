import OMAStatements.S_oeis_a365339

-- Credit: @kumagi

namespace OMA.R_oeis_a365339_R1

open OMA.S_oeis_a365339 Filter

private def lengths (N : ℕ) : Set ℕ :=
  {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    MonotoneOn Nat.totient (A : Set ℕ) ∧ A.card = k}

private lemma lengths_bounded (N : ℕ) : BddAbove (lengths N) := by
  refine ⟨(Finset.Icc 1 N).card, ?_⟩
  rintro k ⟨A, hA, _, rfl⟩
  exact Finset.card_le_card hA

private lemma lengths_nonempty (N : ℕ) : (lengths N).Nonempty := by
  refine ⟨0, ∅, Finset.empty_subset _, ?_, rfl⟩
  intro x hx
  simp at hx

theorem prime_excess_monotone {C N : ℕ} (hCN : C ≤ N) :
    g C + Nat.primeCounting N ≤ g N + Nat.primeCounting C := by
  obtain ⟨A, hA, hmono, hcard⟩ := Nat.sSup_mem (lengths_nonempty C) (lengths_bounded C)
  let P := (Nat.primesLE N).filter (fun p => C < p)
  have hP (p : ℕ) : p ∈ P ↔ p ≤ N ∧ p.Prime ∧ C < p := by
    simp [P, Nat.mem_primesLE, and_assoc]
  have hsub : A ∪ P ⊆ Finset.Icc 1 N := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · have hx := Finset.mem_Icc.mp (hA hx)
      exact Finset.mem_Icc.mpr ⟨hx.1, hx.2.trans hCN⟩
    · obtain ⟨hle, hp, _⟩ := (hP x).mp hx
      exact Finset.mem_Icc.mpr ⟨hp.pos, hle⟩
  have hmono' : MonotoneOn Nat.totient ((A ∪ P : Finset ℕ) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
    obtain hx | hx := hx <;> obtain hy | hy := hy
    · exact hmono hx hy hxy
    · have h₁ := (Finset.mem_Icc.mp (hA hx)).2
      obtain ⟨_, hp, h₂⟩ := (hP y).mp hy
      rw [Nat.totient_prime hp]
      exact (Nat.totient_le x).trans (by omega)
    · have h₁ := (hP x).mp hx |>.2.2
      have h₂ := (Finset.mem_Icc.mp (hA hy)).2
      omega
    · rw [Nat.totient_prime ((hP x).mp hx).2.1, Nat.totient_prime ((hP y).mp hy).2.1]
      omega
  have hd : Disjoint A P := Finset.disjoint_left.mpr (fun x hx hxp =>
    (not_lt_of_ge (Finset.mem_Icc.mp (hA hx)).2) ((hP x).mp hxp).2.2)
  have hsplit : (Nat.primesLE C) ∪ P = Nat.primesLE N := by
    ext x
    simp only [Finset.mem_union, Nat.mem_primesLE, hP]
    by_cases hp : x.Prime <;> simp [hp] <;> omega
  have hpd : Disjoint (Nat.primesLE C) P := Finset.disjoint_left.mpr (fun x hx hxp =>
    (not_lt_of_ge (Nat.mem_primesLE.mp hx).1) ((hP x).mp hxp).2.2)
  have hpc := Finset.card_union_of_disjoint hpd
  rw [hsplit, Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at hpc
  have hg : (A ∪ P).card ≤ g N :=
    le_csSup (lengths_bounded N) ⟨A ∪ P, hsub, hmono', rfl⟩
  rw [Finset.card_union_of_disjoint hd] at hg
  change A.card = g C at hcard
  omega

theorem lower_bound_from_seed
    (h : Nat.primeCounting 31957 + 64 ≤ g 31957) (N : ℕ) (hN : 31957 ≤ N) :
    Nat.primeCounting N + 64 ≤ g N := by
  have := prime_excess_monotone hN
  omega

/-- The finite lower-bound certificate at the first prime of the proposed tail.
Pollack–Pomerance–Treviño, section 9, report a monotone witness of size 3492.
Source: https://math.dartmouth.edu/~carlp/MonotonePhi.pdf -/
def H1 : Prop := Nat.primeCounting 31957 + 64 ≤ g 31957

/-- An upper bound along an unbounded subsequence suffices because excess
over the prime count is nondecreasing. -/
def H2 : Prop := ∃ᶠ N : ℕ in atTop, g N ≤ Nat.primeCounting N + 64

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a365339.main := by
  intro hseed hcofinal n hn
  obtain ⟨N, hN, hupper⟩ := frequently_atTop.mp hcofinal n
  have hmono := prime_excess_monotone hN
  exact le_antisymm (by omega) (lower_bound_from_seed hseed n hn)

end OMA.R_oeis_a365339_R1
