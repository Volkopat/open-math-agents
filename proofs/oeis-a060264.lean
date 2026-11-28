import OMAStatements.S_oeis_a060264

namespace OMA.S_oeis_a060264



theorem a_spec (n : ℕ) : 2 * n < a n ∧ (a n).Prime := by
  have h := Nat.find_spec (Nat.exists_infinite_primes (2 * n + 1))
  exact ⟨by unfold a firstPrimeAfter; omega, h.2⟩

theorem a_le (n p : ℕ) (hp : p.Prime) (h : 2 * n < p) : a n ≤ p :=
  Nat.find_min' (Nat.exists_infinite_primes (2 * n + 1)) ⟨by omega, hp⟩

theorem inj_of_gt {p n : ℕ} (hp : p.Prime) (h : 2 * n < p) :
    Set.InjOn (fun i : ℕ => i ^ 2 % p) (Set.Icc 1 n) := by
  haveI := Fact.mk hp
  intro i hi j hj hij
  simp only [Set.mem_Icc] at hi hj
  simp only at hij
  have hc : ((i : ZMod p)) ^ 2 = ((j : ZMod p)) ^ 2 := by
    have := (ZMod.natCast_eq_natCast_iff' (i ^ 2) (j ^ 2) p).mpr hij
    push_cast at this
    exact this
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc with h1 | h1
  · have := (ZMod.natCast_eq_natCast_iff' i j p).mp h1
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  · have h2 : ((i + j : ℕ) : ZMod p) = 0 := by
      push_cast
      rw [h1]
      ring
    have h3 := (ZMod.natCast_eq_zero_iff (i + j) p).mp h2
    have h4 := Nat.le_of_dvd (by omega) h3
    omega

theorem not_inj_of_le {p n : ℕ} (hp : p.Prime) (h : p ≤ 2 * n) (hn : 2 < n) :
    ¬ Set.InjOn (fun i : ℕ => i ^ 2 % p) (Set.Icc 1 n) := by
  intro hinj
  rcases hp.eq_two_or_odd' with h2 | hodd
  · subst h2
    have := hinj (show (1 : ℕ) ∈ Set.Icc 1 n by simp only [Set.mem_Icc]; omega)
      (show (3 : ℕ) ∈ Set.Icc 1 n by simp only [Set.mem_Icc]; omega) (by decide)
    omega
  · have hp3 := hp.two_le
    have ho : p % 2 = 1 := Nat.odd_iff.mp hodd
    set i := p / 2 with hi
    set j := p / 2 + 1 with hj
    have hij : i + j = p := by omega
    have hsq : i ^ 2 % p = j ^ 2 % p := by
      rw [← hij]
      have e : j ^ 2 + (i + j) * (2 * i) = i ^ 2 + (i + j) * (i + j) := by ring
      have e1 := Nat.add_mul_mod_self_left (j ^ 2) (i + j) (2 * i)
      have e2 := Nat.add_mul_mod_self_left (i ^ 2) (i + j) (i + j)
      rw [e] at e1
      rw [← e1, e2]
    have := hinj (show i ∈ Set.Icc 1 n by simp only [Set.mem_Icc]; omega)
      (show j ∈ Set.Icc 1 n by simp only [Set.mem_Icc]; omega) hsq
    omega

/-- The conjecture of the comment. -/
theorem conjecture (n : ℕ) (hn : 2 < n) :
    IsLeast {p : ℕ | p.Prime ∧ Set.InjOn (fun i : ℕ => i ^ 2 % p) (Set.Icc 1 n)} (a n) := by
  refine ⟨⟨(a_spec n).2, inj_of_gt (a_spec n).2 (a_spec n).1⟩, ?_⟩
  rintro p ⟨hp, hinj⟩
  apply a_le n p hp
  by_contra hle
  push_neg at hle
  exact not_inj_of_le hp hle hn hinj

end OMA.S_oeis_a060264

theorem OMA.solution : type_of% @OMA.S_oeis_a060264.main :=
  fun n hn => OMA.S_oeis_a060264.conjecture n hn
