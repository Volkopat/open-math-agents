import OMAStatements.S_oeis_a106505

-- Problem: A106505: Ordered and uniqued length of side common to the two angles, one being the double of the other, of a primitive integer-sided trian
-- Upstream: formal-conjectures statements/oeis-a106505.lean:0 (declaration OMA.S_oeis_a106505.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with s = r + D, s^2 - r^2 = D * (2r + D). If D is odd the value is odd and at
-- least 5; if D is even, r is odd (gcd(r, s) = 1) and the value is a multiple of 8 and at least
-- 16. Conversely 2j + 1 = (j+1)^2 - j^2 for j >= 2 and 8i + 16 = (2i+5)^2 - (2i+3)^2. So the
-- terms are the odd numbers >= 5 and the multiples of 8 that are >= 16, the number of terms
-- below m is (m/2 - 2) + ((m+7)/8 - 2), and a term t >= 9 has t + 8 as the term five places on.

open OMA.S_oeis_a106505 in
theorem OMA.solution : type_of% @OMA.S_oeis_a106505.main := by
  classical
  have hchar : ∀ m : ℕ, IsTerm m ↔ ((m % 2 = 1 ∧ 5 ≤ m) ∨ (m % 8 = 0 ∧ 16 ≤ m)) := by
    intro m
    constructor
    · rintro ⟨r, s, hrs, _hs2, hcop, rfl⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hrs
      have hm : (r + d + 1) ^ 2 - r ^ 2 = (d + 1) * (2 * r + d + 1) :=
        Nat.sub_eq_of_eq_add (by ring)
      rw [hm]
      obtain ⟨P, hP⟩ : ∃ P, P = (d + 1) * (2 * r + d + 1) := ⟨_, rfl⟩
      rw [← hP]
      rcases Nat.even_or_odd' d with ⟨e, rfl | rfl⟩
      · have h1 : P = 2 * (2 * e * r + 2 * e * e + 2 * e + r) + 1 := by
          rw [hP]
          ring
        have h2 : P = (2 * r + 2 * e + 1) + 2 * e * (2 * r + 2 * e + 1) := by
          rw [hP]
          ring
        left
        constructor
        · omega
        · omega
      · right
        rcases Nat.even_or_odd' r with ⟨g, rfl | rfl⟩
        · exfalso
          have h2r : 2 ∣ 2 * g := ⟨g, rfl⟩
          have h2s : 2 ∣ 2 * g + (2 * e + 1) + 1 := ⟨g + e + 1, by ring⟩
          have h3 := Nat.dvd_gcd h2r h2s
          rw [Nat.Coprime.gcd_eq_one hcop] at h3
          omega
        · rcases Nat.even_or_odd' e with ⟨f, rfl | rfl⟩
          · have h1 : P = 8 * ((2 * f + 1) * (g + f + 1)) := by
              rw [hP]
              ring
            have h2 : (2 * f + 1) * (g + f + 1) = (g + f + 1) + 2 * f * (g + f + 1) := by
              ring
            constructor
            · omega
            · omega
          · have h1 : P = 8 * ((f + 1) * (2 * g + 2 * f + 3)) := by
              rw [hP]
              ring
            have h2 : (f + 1) * (2 * g + 2 * f + 3) =
                (2 * g + 2 * f + 3) + f * (2 * g + 2 * f + 3) := by
              ring
            constructor
            · omega
            · omega
    · rintro (⟨_, _⟩ | ⟨_, _⟩)
      · obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := ⟨m / 2, by omega⟩
        refine ⟨j, j + 1, by omega, by omega,
          Nat.coprime_self_add_right.mpr (Nat.coprime_one_right j), ?_⟩
        exact (Nat.sub_eq_of_eq_add (by ring)).symm
      · obtain ⟨i, rfl⟩ : ∃ i, m = 8 * i + 16 := ⟨m / 8 - 2, by omega⟩
        have hc : Nat.Coprime (2 * i + 3) (2 * i + 5) := by
          rw [show 2 * i + 5 = 2 * i + 3 + 2 by ring, Nat.coprime_self_add_right,
            show 2 * i + 3 = 1 + (i + 1) * 2 by ring]
          exact (Nat.coprime_add_mul_right_left 1 2 (i + 1)).mpr (Nat.coprime_one_left 2)
        refine ⟨2 * i + 3, 2 * i + 5, by omega, by omega, hc, ?_⟩
        exact (Nat.sub_eq_of_eq_add (by ring)).symm
  have hcount : ∀ m : ℕ, Nat.count IsTerm m = (m / 2 - 2) + ((m + 7) / 8 - 2) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.count_succ, ih]
      by_cases h : IsTerm m
      · rw [if_pos h]
        rcases (hchar m).mp h with ⟨_, _⟩ | ⟨_, _⟩
        · omega
        · omega
      · rw [if_neg h]
        rw [hchar] at h
        omega
  have hinf : (Set.ofPred IsTerm).Infinite := by
    have hm : StrictMono (fun j : ℕ => 2 * j + 5) := by
      apply strictMono_nat_of_lt_succ
      intro j
      show 2 * j + 5 < 2 * (j + 1) + 5
      omega
    exact Set.infinite_of_injective_forall_mem hm.injective (fun j =>
      show 2 * j + 5 ∈ Set.ofPred IsTerm from
        (hchar (2 * j + 5)).mpr (Or.inl ⟨by omega, by omega⟩))
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  show Nat.nth IsTerm (k + 3 + 5 - 1) = Nat.nth IsTerm (k + 3 - 1) + 8
  rw [show k + 3 + 5 - 1 = k + 2 + 5 by omega, show k + 3 - 1 = k + 2 by omega]
  obtain ⟨t, ht⟩ : ∃ t, t = Nat.nth IsTerm (k + 2) := ⟨_, rfl⟩
  rw [← ht]
  have hpt : IsTerm t := by
    rw [ht]
    exact Nat.nth_mem_of_infinite hinf (k + 2)
  have hct : Nat.count IsTerm t = k + 2 := by
    rw [ht]
    exact Nat.count_nth_of_infinite hinf (k + 2)
  rw [hcount] at hct
  have hq := (hchar t).mp hpt
  have ht9 : 9 ≤ t := by
    rcases hq with ⟨_, _⟩ | ⟨_, _⟩
    · omega
    · omega
  have hpt8 : IsTerm (t + 8) := by
    rw [hchar]
    rcases hq with ⟨_, _⟩ | ⟨_, _⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hc8 : Nat.count IsTerm (t + 8) = k + 2 + 5 := by
    rw [hcount]
    omega
  rw [← hc8]
  exact Nat.nth_count hpt8
