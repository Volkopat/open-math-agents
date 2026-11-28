import OMAReductions.R_oeis_a084017_R1

-- Reduction oeis-a084017.R1.H1.R1 of the `~ 10 | n` direction of OEIS A084017

/-!
# Split of the Murthy-Srikanth construction for `n` not divisible by 10

Write `n = 2 ^ a * 5 ^ b * 3 ^ v * m` with `m` coprime to 30. The merged proof
dispatches on the residue class of `(a, b, v, m)`:

* `H1` : the hard family `1 <= a`, `b = 0`, `11 | m or 101 | m` - the closed
  branches `hard_closed_v0/v1/v234/v5` (per-family CRT constructions).
* `H2` : the open cases `v = 0` and the hard family - `hres_open` plus its
  `assemble_v0*` capacity constructions, taking `H1` as a premise.
* `H3` : the remaining cases, all discharged by finite certificates -
  `hres_fin` and its `hres_fin_R*` witness lemmas.
* `H4` : the dispatcher itself - `A084017_of_residue`: every non-residual
  class is covered by an `assemble_*` family, residual classes are passed to
  the provided prover.

`main` is the case split `residualCase -> residualOpen or residualFin`,
then `relaxedGoal -> finGoal` since `10` does not divide `n`.
-/

namespace OMA.R_oeis_a084017_R1_H1_R1

/-- The hard family: `a >= 1`, `b = 0`, `11` or `101` divides `m`. -/
def H1 : Prop :=
  ∀ a b v m : ℕ, m.Coprime 30 → 1 ≤ a ∧ b = 0 ∧ (11 ∣ m ∨ 101 ∣ m) →
    ∃ P z : ℕ, P ≠ 0
      ∧ z = OMA.S_oeis_a084017.tz (2 ^ a * 5 ^ b * 3 ^ v * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ a * 5 ^ b * 3 ^ v * m
      ∧ 2 ^ a * 5 ^ b * 3 ^ v * m ∣ P * 10 ^ z
      ∧ 2 ^ a * 5 ^ b * 3 ^ v * m ∣ (Nat.digits 10 P).sum

/-- The open cases `v = 0` and the hard family, given `H1`. -/
def H2 : Prop :=
  (∀ a b v m : ℕ, m.Coprime 30 → 1 ≤ a ∧ b = 0 ∧ (11 ∣ m ∨ 101 ∣ m) →
    ∃ P z : ℕ, P ≠ 0
      ∧ z = OMA.S_oeis_a084017.tz (2 ^ a * 5 ^ b * 3 ^ v * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ a * 5 ^ b * 3 ^ v * m
      ∧ 2 ^ a * 5 ^ b * 3 ^ v * m ∣ P * 10 ^ z
      ∧ 2 ^ a * 5 ^ b * 3 ^ v * m ∣ (Nat.digits 10 P).sum) →
  ∀ n a b v m : ℕ, n = 2 ^ a * 5 ^ b * 3 ^ v * m → m.Coprime 30 →
    v = 0 ∨ (1 ≤ a ∧ b = 0 ∧ (11 ∣ m ∨ 101 ∣ m)) →
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ n)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = n
      ∧ n ∣ P * 10 ^ z
      ∧ n ∣ (Nat.digits 10 P).sum

/-- The eight remaining residue classes, discharged by finite certificates. -/
def H3 : Prop :=
  ∀ n a b v m : ℕ, n = 2 ^ a * 5 ^ b * 3 ^ v * m → m.Coprime 30 →
    (a = 0 ∧ 2 ≤ v ∧ v ≤ 4
        ∧ ¬ (8 * b + 44 ≤ 5 ^ b * m * 3 ^ (v - 2)) ∧ (b ≠ 0 ∨ m ≠ 1))
      ∨ (1 ≤ a ∧ 1 ≤ b ∧ 2 ≤ v ∧ v ≤ 4
        ∧ ¬ (36 * 2 ^ (a - 2) ≤ 2 * (2 ^ a * 5 ^ b * 3 ^ (v - 2) * m)))
      ∨ (1 ≤ a ∧ b = 0 ∧ 2 ≤ v ∧ v ≤ 4
        ∧ ¬ (4 * a + 6 ≤ 2 ^ a * 3 ^ (v - 2) * m))
      ∨ (1 ≤ a ∧ 1 ≤ b ∧ v = 1
        ∧ ¬ (4 * m + 39 + 36 * 2 ^ (a - 2) + (a + b)
            ≤ 2 * (2 ^ a * 5 ^ b * m)))
      ∨ (a = 0 ∧ 1 ≤ b ∧ v = 1 ∧ ¬ (4 * m + 8 * b + 41 ≤ 5 ^ b * m))
      ∨ (a = 0 ∧ b = 0 ∧ v = 1 ∧ ¬ (8 * ((m - 1) / 9 + 1) + 41 ≤ m))
      ∨ (2 ≤ a ∧ b = 0 ∧ v = 1
        ∧ ¬ (4 * m + 2 ^ a + 8 * a + 8 + 2 ^ a * m ≤ 3 * (2 ^ a * m)))
      ∨ (a = 1 ∧ b = 0 ∧ v = 1 ∧ ¬ (8 * ((m - 1) / 9 + 1) + 18 ≤ 2 * m)) →
    ∃ P z : ℕ, P ≠ 0
      ∧ z = OMA.S_oeis_a084017.tz n
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = n
      ∧ n ∣ P * 10 ^ z
      ∧ n ∣ (Nat.digits 10 P).sum

/-- The dispatcher: given a prover for the residual classes, every nonzero `n`
    admits a palindromic multiple (zero count only bounded by `10 | n`). -/
def H4 : Prop :=
  ∀ n : ℕ, (∀ a b v m : ℕ, n = 2 ^ a * 5 ^ b * 3 ^ v * m → m.Coprime 30 →
    v = 0
      ∨ (1 ≤ a ∧ b = 0 ∧ (11 ∣ m ∨ 101 ∣ m))
      ∨ (a = 0 ∧ 2 ≤ v ∧ v ≤ 4
        ∧ ¬ (8 * b + 44 ≤ 5 ^ b * m * 3 ^ (v - 2)) ∧ (b ≠ 0 ∨ m ≠ 1))
      ∨ (1 ≤ a ∧ 1 ≤ b ∧ 2 ≤ v ∧ v ≤ 4
        ∧ ¬ (36 * 2 ^ (a - 2) ≤ 2 * (2 ^ a * 5 ^ b * 3 ^ (v - 2) * m)))
      ∨ (1 ≤ a ∧ b = 0 ∧ 2 ≤ v ∧ v ≤ 4
        ∧ ¬ (4 * a + 6 ≤ 2 ^ a * 3 ^ (v - 2) * m))
      ∨ (1 ≤ a ∧ 1 ≤ b ∧ v = 1
        ∧ ¬ (4 * m + 39 + 36 * 2 ^ (a - 2) + (a + b)
            ≤ 2 * (2 ^ a * 5 ^ b * m)))
      ∨ (a = 0 ∧ 1 ≤ b ∧ v = 1 ∧ ¬ (4 * m + 8 * b + 41 ≤ 5 ^ b * m))
      ∨ (a = 0 ∧ b = 0 ∧ v = 1 ∧ ¬ (8 * ((m - 1) / 9 + 1) + 41 ≤ m))
      ∨ (2 ≤ a ∧ b = 0 ∧ v = 1
        ∧ ¬ (4 * m + 2 ^ a + 8 * a + 8 + 2 ^ a * m ≤ 3 * (2 ^ a * m)))
      ∨ (a = 1 ∧ b = 0 ∧ v = 1 ∧ ¬ (8 * ((m - 1) / 9 + 1) + 18 ≤ 2 * m)) →
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ n)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = n
      ∧ n ∣ P * 10 ^ z
      ∧ n ∣ (Nat.digits 10 P).sum) →
    n ≠ 0 →
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ n)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = n
      ∧ n ∣ P * 10 ^ z
      ∧ n ∣ (Nat.digits 10 P).sum

lemma tz_zero_of_not_dvd' {n : ℕ} (h : ¬ 10 ∣ n) :
    OMA.S_oeis_a084017.tz n = 0 := by
  have hmod : n % 10 ≠ 0 := fun e => h (Nat.dvd_of_mod_eq_zero e)
  show ((Nat.digits 10 n).takeWhile (· = 0)).length = 0
  cases hd : Nat.digits 10 n with
  | nil => rfl
  | cons d ds =>
    have hn0 : 0 < n := Nat.pos_of_ne_zero (fun e => by
      rw [e, Nat.digits_zero] at hd
      exact nomatch hd)
    have hdmod : n % 10 = d := by
      have hdd := Nat.digits_def' (b := 10) (by norm_num) hn0
      rw [hd] at hdd
      exact (List.cons.inj hdd).1.symm
    rw [List.takeWhile_cons]
    have hd0 : d ≠ 0 := fun e => hmod (hdmod.trans e)
    simp [hd0]

lemma dvd10_of_tz_pos' {n : ℕ} (h : 0 < OMA.S_oeis_a084017.tz n) : 10 ∣ n := by
  by_contra hn
  rw [tz_zero_of_not_dvd' hn] at h
  exact Nat.lt_irrefl 0 h

lemma rel_of_fin {n : ℕ}
    (h : ∃ P z : ℕ, P ≠ 0
      ∧ z = OMA.S_oeis_a084017.tz n
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = n
      ∧ n ∣ P * 10 ^ z
      ∧ n ∣ (Nat.digits 10 P).sum) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ n)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = n
      ∧ n ∣ P * 10 ^ z
      ∧ n ∣ (Nat.digits 10 P).sum := by
  obtain ⟨P, z, hP, hz, hpal, hlen, hdvd, hσ⟩ := h
  exact ⟨P, z, hP, fun hz0 => dvd10_of_tz_pos' (hz ▸ hz0), hpal, hlen, hdvd, hσ⟩

lemma fin_of_rel {n : ℕ} (h10 : ¬ 10 ∣ n)
    (h : ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ n)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = n
      ∧ n ∣ P * 10 ^ z
      ∧ n ∣ (Nat.digits 10 P).sum) :
    OMA.S_oeis_a084017.qualifies n := by
  obtain ⟨P, z, hP, hz, hpal, hlen, hdvd, hσ⟩ := h
  have hz0 : z = 0 := by
    rcases Nat.eq_zero_or_pos z with e | hp
    · exact e
    · exact absurd (hz hp) h10
  subst hz0
  refine ⟨P, 0, hP, (tz_zero_of_not_dvd' h10).symm, hpal, ?_, ?_, hσ⟩
  · simpa using hlen
  · simpa using hdvd

lemma case_or {a b v m : ℕ}
    (h : v = 0
      ∨ (1 ≤ a ∧ b = 0 ∧ (11 ∣ m ∨ 101 ∣ m))
      ∨ (a = 0 ∧ 2 ≤ v ∧ v ≤ 4
        ∧ ¬ (8 * b + 44 ≤ 5 ^ b * m * 3 ^ (v - 2)) ∧ (b ≠ 0 ∨ m ≠ 1))
      ∨ (1 ≤ a ∧ 1 ≤ b ∧ 2 ≤ v ∧ v ≤ 4
        ∧ ¬ (36 * 2 ^ (a - 2) ≤ 2 * (2 ^ a * 5 ^ b * 3 ^ (v - 2) * m)))
      ∨ (1 ≤ a ∧ b = 0 ∧ 2 ≤ v ∧ v ≤ 4
        ∧ ¬ (4 * a + 6 ≤ 2 ^ a * 3 ^ (v - 2) * m))
      ∨ (1 ≤ a ∧ 1 ≤ b ∧ v = 1
        ∧ ¬ (4 * m + 39 + 36 * 2 ^ (a - 2) + (a + b)
            ≤ 2 * (2 ^ a * 5 ^ b * m)))
      ∨ (a = 0 ∧ 1 ≤ b ∧ v = 1 ∧ ¬ (4 * m + 8 * b + 41 ≤ 5 ^ b * m))
      ∨ (a = 0 ∧ b = 0 ∧ v = 1 ∧ ¬ (8 * ((m - 1) / 9 + 1) + 41 ≤ m))
      ∨ (2 ≤ a ∧ b = 0 ∧ v = 1
        ∧ ¬ (4 * m + 2 ^ a + 8 * a + 8 + 2 ^ a * m ≤ 3 * (2 ^ a * m)))
      ∨ (a = 1 ∧ b = 0 ∧ v = 1 ∧ ¬ (8 * ((m - 1) / 9 + 1) + 18 ≤ 2 * m))) :
    (v = 0 ∨ (1 ≤ a ∧ b = 0 ∧ (11 ∣ m ∨ 101 ∣ m)))
      ∨ ((a = 0 ∧ 2 ≤ v ∧ v ≤ 4
        ∧ ¬ (8 * b + 44 ≤ 5 ^ b * m * 3 ^ (v - 2)) ∧ (b ≠ 0 ∨ m ≠ 1))
      ∨ (1 ≤ a ∧ 1 ≤ b ∧ 2 ≤ v ∧ v ≤ 4
        ∧ ¬ (36 * 2 ^ (a - 2) ≤ 2 * (2 ^ a * 5 ^ b * 3 ^ (v - 2) * m)))
      ∨ (1 ≤ a ∧ b = 0 ∧ 2 ≤ v ∧ v ≤ 4
        ∧ ¬ (4 * a + 6 ≤ 2 ^ a * 3 ^ (v - 2) * m))
      ∨ (1 ≤ a ∧ 1 ≤ b ∧ v = 1
        ∧ ¬ (4 * m + 39 + 36 * 2 ^ (a - 2) + (a + b)
            ≤ 2 * (2 ^ a * 5 ^ b * m)))
      ∨ (a = 0 ∧ 1 ≤ b ∧ v = 1 ∧ ¬ (4 * m + 8 * b + 41 ≤ 5 ^ b * m))
      ∨ (a = 0 ∧ b = 0 ∧ v = 1 ∧ ¬ (8 * ((m - 1) / 9 + 1) + 41 ≤ m))
      ∨ (2 ≤ a ∧ b = 0 ∧ v = 1
        ∧ ¬ (4 * m + 2 ^ a + 8 * a + 8 + 2 ^ a * m ≤ 3 * (2 ^ a * m)))
      ∨ (a = 1 ∧ b = 0 ∧ v = 1 ∧ ¬ (8 * ((m - 1) / 9 + 1) + 18 ≤ 2 * m))) := by
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr h)))))))

theorem main : H1 → H2 → H3 → H4 → OMA.R_oeis_a084017_R1.H1 := by
  intro h1 h2 h3 h4 n hn h10
  refine fin_of_rel h10 ?_
  refine h4 n ?_ hn
  intro a b v m hnd hm30 hc
  rcases (case_or hc) with ho | hf
  · exact h2 h1 n a b v m hnd hm30 ho
  · exact rel_of_fin (h3 n a b v m hnd hm30 hf)

end OMA.R_oeis_a084017_R1_H1_R1
