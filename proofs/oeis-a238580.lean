import OMAStatements.S_oeis_a238580

-- Problem: A238580: a(n) = |{0 < k <= n: 2*k + 1 and prime(k)*prime(n) - 2 are both prime}|.
-- Upstream: formal-conjectures statements/oeis-a238580.lean:0 (declaration OMA.S_oeis_a238580.main)
-- Credit: @azmiozgen (the owner of the agent is credited as the solver)
-- Refutation: a(29) = 1 (only k = 8 works), but 29 is not in the printed list.

open OMA.S_oeis_a238580 in
/-- `prime k = v` from `v` prime and `π(v - 1)` primes below `v`. -/
lemma OMA.pr {k v : ℕ} (hv : v.Prime) (hc : Nat.count Nat.Prime v = k - 1) : prime k = v := by
  unfold prime; rw [← hc, Nat.nth_count hv]

set_option maxRecDepth 100000 in
open OMA.S_oeis_a238580 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a238580.main) := by
  rintro ⟨-, h⟩
  have p1 : prime 1 = 2 := OMA.pr (by norm_num) (by decide)
  have p2 : prime 2 = 3 := OMA.pr (by norm_num) (by decide)
  have p3 : prime 3 = 5 := OMA.pr (by norm_num) (by decide)
  have p4 : prime 4 = 7 := OMA.pr (by norm_num) (by decide)
  have p5 : prime 5 = 11 := OMA.pr (by norm_num) (by decide)
  have p6 : prime 6 = 13 := OMA.pr (by norm_num) (by decide)
  have p7 : prime 7 = 17 := OMA.pr (by norm_num) (by decide)
  have p8 : prime 8 = 19 := OMA.pr (by norm_num) (by decide)
  have p9 : prime 9 = 23 := OMA.pr (by norm_num) (by decide)
  have p10 : prime 10 = 29 := OMA.pr (by norm_num) (by decide)
  have p11 : prime 11 = 31 := OMA.pr (by norm_num) (by decide)
  have p12 : prime 12 = 37 := OMA.pr (by norm_num) (by decide)
  have p13 : prime 13 = 41 := OMA.pr (by norm_num) (by decide)
  have p14 : prime 14 = 43 := OMA.pr (by norm_num) (by decide)
  have p15 : prime 15 = 47 := OMA.pr (by norm_num) (by decide)
  have p16 : prime 16 = 53 := OMA.pr (by norm_num) (by decide)
  have p17 : prime 17 = 59 := OMA.pr (by norm_num) (by decide)
  have p18 : prime 18 = 61 := OMA.pr (by norm_num) (by decide)
  have p19 : prime 19 = 67 := OMA.pr (by norm_num) (by decide)
  have p20 : prime 20 = 71 := OMA.pr (by norm_num) (by decide)
  have p21 : prime 21 = 73 := OMA.pr (by norm_num) (by decide)
  have p22 : prime 22 = 79 := OMA.pr (by norm_num) (by decide)
  have p23 : prime 23 = 83 := OMA.pr (by norm_num) (by decide)
  have p24 : prime 24 = 89 := OMA.pr (by norm_num) (by decide)
  have p25 : prime 25 = 97 := OMA.pr (by norm_num) (by decide)
  have p26 : prime 26 = 101 := OMA.pr (by norm_num) (by decide)
  have p27 : prime 27 = 103 := OMA.pr (by norm_num) (by decide)
  have p28 : prime 28 = 107 := OMA.pr (by norm_num) (by decide)
  have p29 : prime 29 = 109 := OMA.pr (by norm_num) (by decide)
  have h29 : a 29 = 1 := by
    unfold a
    rw [Finset.card_eq_one]
    refine ⟨8, ?_⟩
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, p29]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp, hq⟩
      interval_cases k
      all_goals try simp only [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16,
        p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29] at hq
      all_goals try rfl
      all_goals try (norm_num at hp; done)
      all_goals norm_num at hq
    · rintro rfl
      exact ⟨by norm_num, by norm_num, by rw [p8]; norm_num⟩
  have := h 29 (by norm_num) h29
  simp at this
