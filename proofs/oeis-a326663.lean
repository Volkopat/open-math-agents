import OMAStatements.S_oeis_a326663
import Mathlib

-- Problem: OEIS A326663, conjecture of Kimberling: for the solution of the complementary
-- equation c(n) = a(n) + b(2n) (a and b least new), 7n - c(n) is 1 or 2 for each n >= 1.
-- Statement: statements/oeis-a326663.lean (declaration OMA.S_oeis_a326663.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let dl(n) = 2 if 3 does not divide n and dl(3i) = 3 - dl(i); dl is 1 or 2. Let
-- Cc(n) = 7n - dl(n), and let Af(3i+1) = 7i + 1, Af(3i+2) = 7i + 3, Af(3i+3) = 7i + 4 + dl(i+1).
-- Invariant: after step n, c(n) = Cc(n), a(m) = Af(m) for m <= 2n, and the placed numbers are
-- {1, ..., M} and the Cc(i), 1 <= i <= n, with M = 14J, 14J + 4, 14J + 9 for n = 3J, 3J + 1,
-- 3J + 2. Each block 7t - 6, ..., 7t has exactly one number Cc(t), at 7t - 2 or 7t - 1.
-- Step 3J + 1 places 14J + 1, ..., 14J + 4. Step 3J + 2 places the number of 14J + 5, 14J + 6
-- that is not Cc(2J+1), and 14J + 7, 14J + 8, 14J + 9. Step 3J + 3 places 14J + 10, 14J + 11,
-- the number of 14J + 12, 14J + 13 that is not Cc(2J+2), and 14J + 14. In each case
-- a(n) + b(2n) = Af(n) + (last placed number) = Cc(n).

namespace OMA.A326663

open OMA.S_oeis_a326663

lemma mex_eq (s : Finset ℕ) (m : ℕ) (hm : 0 < m) (hns : m ∉ s)
    (hall : ∀ k, 0 < k → k < m → k ∈ s) : leastNew s = m := by
  unfold leastNew
  apply le_antisymm
  · exact Nat.sInf_le ⟨hm, hns⟩
  · refine le_csInf ⟨m, hm, hns⟩ ?_
    rintro k ⟨hk, hks⟩
    by_contra hlt
    exact hks (hall k hk (by omega))

/-- One more least new number: if x is new and the gap below x is filled. -/
lemma mex_insert (U : Finset ℕ) (w x : ℕ) (hw : leastNew U = w) (hwx : w < x) (hw0 : 0 < w)
    (hwU : w ∉ U) (hxU : x ∉ U) (hlow : ∀ k, 0 < k → k < w → k ∈ U)
    (hgap : ∀ k, w < k → k < x → k ∈ U) :
    leastNew (insert w U) = x ∧ x ∉ insert w U ∧ ∀ k, 0 < k → k < x → k ∈ insert w U := by
  have hall : ∀ k, 0 < k → k < x → k ∈ insert w U := by
    intro k hk hlt
    rw [Finset.mem_insert]
    rcases Nat.lt_trichotomy k w with h | h | h
    · right; exact hlow k hk h
    · left; exact h
    · right; exact hgap k h hlt
  have hnot : x ∉ insert w U := by
    rw [Finset.mem_insert]; rintro (h | h)
    · omega
    · exact hxU h
  exact ⟨mex_eq _ _ (by omega) hnot hall, hnot, hall⟩

/-- Four least new numbers in a row. -/
lemma four_mex (U : Finset ℕ) (w x y z : ℕ) (hw : 0 < w) (hwx : w < x) (hxy : x < y) (hyz : y < z)
    (hwU : w ∉ U) (hxU : x ∉ U) (hyU : y ∉ U) (hzU : z ∉ U)
    (h1 : ∀ k, 0 < k → k < w → k ∈ U) (h2 : ∀ k, w < k → k < x → k ∈ U)
    (h3 : ∀ k, x < k → k < y → k ∈ U) (h4 : ∀ k, y < k → k < z → k ∈ U) :
    leastNew U = w ∧ leastNew (insert w U) = x ∧ leastNew (insert x (insert w U)) = y ∧
    leastNew (insert y (insert x (insert w U))) = z := by
  have m1 := mex_eq U w hw hwU h1
  obtain ⟨m2, n2, l2⟩ := mex_insert U w x m1 hwx hw hwU hxU h1 h2
  obtain ⟨m3, n3, l3⟩ := mex_insert (insert w U) x y m2 hxy (by omega) n2
    (by rw [Finset.mem_insert]; rintro (h | h); omega; exact hyU h) l2
    (fun k hk1 hk2 => by rw [Finset.mem_insert]; right; exact h3 k hk1 hk2)
  obtain ⟨m4, -, -⟩ := mex_insert (insert x (insert w U)) y z m3 hyz (by omega) n3
    (by rw [Finset.mem_insert, Finset.mem_insert]; rintro (h | h | h); omega; omega; exact hzU h) l3
    (fun k hk1 hk2 => by
      rw [Finset.mem_insert, Finset.mem_insert]; right; right; exact h4 k hk1 hk2)
  exact ⟨m1, m2, m3, m4⟩

/-- The correction term: c(n) = 7 n - dl(n). -/
def dl : ℕ → ℕ
  | n => if h : n = 0 then 0 else if h' : n % 3 ≠ 0 then 2 else 3 - dl (n / 3)
decreasing_by omega

lemma dl1 (i : ℕ) : dl (3 * i + 1) = 2 := by
  rw [dl, dif_neg (by omega), dif_pos (by omega)]

lemma dl2 (i : ℕ) : dl (3 * i + 2) = 2 := by
  rw [dl, dif_neg (by omega), dif_pos (by omega)]

lemma dl3 (i : ℕ) : dl (3 * i + 3) = 3 - dl (i + 1) := by
  rw [dl, dif_neg (by omega), dif_neg (by omega), show (3 * i + 3) / 3 = i + 1 by omega]

lemma dl_range : ∀ n : ℕ, 1 ≤ n → dl n = 1 ∨ dl n = 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨i, hi⟩ : ∃ i, n = 3 * i + 1 ∨ n = 3 * i + 2 ∨ n = 3 * i + 3 := ⟨(n - 1) / 3, by omega⟩
    rcases hi with rfl | rfl | rfl
    · rw [dl1]; right; rfl
    · rw [dl2]; right; rfl
    · have := ih (i + 1) (by omega) (by omega)
      rw [dl3]; omega

/-- The closed form of c. -/
def Cc (n : ℕ) : ℕ := 7 * n - dl n

/-- The closed form of a. -/
def Af (m : ℕ) : ℕ :=
  if m % 3 = 1 then 7 * ((m + 2) / 3) - 6
  else if m % 3 = 2 then 7 * ((m + 2) / 3) - 4
  else 7 * (m / 3) - 3 + dl (m / 3)

lemma Af1 (i : ℕ) : Af (3 * i + 1) = 7 * i + 1 := by
  unfold Af; rw [if_pos (by omega)]; omega

lemma Af2 (i : ℕ) : Af (3 * i + 2) = 7 * i + 3 := by
  unfold Af; rw [if_neg (by omega), if_pos (by omega)]; omega

lemma Af3 (i : ℕ) : Af (3 * i + 3) = 7 * i + 4 + dl (i + 1) := by
  unfold Af
  rw [if_neg (by omega), if_neg (by omega), show (3 * i + 3) / 3 = i + 1 by omega]; omega

/-- The placed set: the numbers up to M and the numbers Cc i with 1 <= i <= n. -/
def Good (U : Finset ℕ) (M n : ℕ) : Prop :=
  ∀ k, k ∈ U ↔ (1 ≤ k ∧ k ≤ M) ∨ ∃ i, 1 ≤ i ∧ i ≤ n ∧ k = Cc i

/-- The invariant after step n. -/
def Inv (n M : ℕ) : Prop :=
  ∃ (α β : ℕ → ℕ) (U : Finset ℕ), state n = (α, β, Cc n, U) ∧ Good U M n ∧
    ∀ m, 1 ≤ m → m ≤ 2 * n → α m = Af m

lemma gen_step (n M M' w x y z : ℕ) (hinv : Inv n M)
    (hfour : ∀ U, Good U M n → (0 < w ∧ w < x ∧ x < y ∧ y < z) ∧
      (w ∉ U ∧ x ∉ U ∧ y ∉ U ∧ z ∉ U) ∧
      (∀ k, 0 < k → k < w → k ∈ U) ∧ (∀ k, w < k → k < x → k ∈ U) ∧
      (∀ k, x < k → k < y → k ∈ U) ∧ (∀ k, y < k → k < z → k ∈ U) ∧
      (∀ k, M < k → k ≤ M' → k = w ∨ k = x ∨ k = y ∨ k = z ∨ k ∈ U))
    (hAw : Af (2 * n + 1) = w) (hAy : Af (2 * n + 2) = y)
    (hD : Cc (n + 1) = Af (n + 1) + z) (hM : M ≤ M') (hzM : z ≤ M') :
    Inv (n + 1) M' := by
  obtain ⟨α0, β0, U, hst, hU, hα⟩ := hinv
  obtain ⟨⟨hw, hwx, hxy, hyz⟩, ⟨hwU, hxU, hyU, hzU⟩, h1, h2, h3, h4, hfill⟩ := hfour U hU
  obtain ⟨m1, m2, m3, m4⟩ := four_mex U w x y z hw hwx hxy hyz hwU hxU hyU hzU h1 h2 h3 h4
  have hα' : ∀ m, 1 ≤ m → m ≤ 2 * (n + 1) →
      Function.update (Function.update α0 (2 * n + 1) w) (2 * n + 2) y m = Af m := by
    intro m hm1 hm2
    rcases Nat.lt_trichotomy m (2 * n + 1) with h | h | h
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hα m hm1 (by omega)
    · rw [h, Function.update_of_ne (by omega), Function.update_self, hAw]
    · rw [show m = 2 * n + 2 by omega, Function.update_self, hAy]
  have hst' : state (n + 1) =
      (Function.update (Function.update α0 (2 * n + 1) w) (2 * n + 2) y,
       Function.update (Function.update β0 (2 * n + 1) x) (2 * n + 2) z,
       Cc (n + 1),
       insert (Cc (n + 1)) (insert z (insert y (insert x (insert w U))))) := by
    rw [state, hst]
    simp only [m1, m2, m3, m4]
    rw [hα' (n + 1) (by omega) (by omega), Function.update_self, ← hD]
  refine ⟨_, _, _, hst', ?_, hα'⟩
  intro k
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_insert, hU]
  constructor
  · rintro (h | h | h | h | h | ⟨h, h'⟩ | ⟨i, hi1, hi, hk⟩)
    · right; exact ⟨n + 1, by omega, le_rfl, h⟩
    · left; omega
    · left; omega
    · left; omega
    · left; omega
    · left; omega
    · right; exact ⟨i, hi1, by omega, hk⟩
  · rintro (⟨hk1, hk2⟩ | ⟨i, hi1, hi, hk⟩)
    · rcases Nat.lt_or_ge M k with hlt | hge
      · rcases hfill k hlt hk2 with h | h | h | h | h
        · right; right; right; right; left; exact h
        · right; right; right; left; exact h
        · right; right; left; exact h
        · right; left; exact h
        · right; right; right; right; right; exact (hU k).mp h
      · right; right; right; right; right; left; exact ⟨hk1, hge⟩
    · rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · right; right; right; right; right; right; exact ⟨i, hi1, by omega, hk⟩
      · left; rw [hk, show i = n + 1 by omega]

/-- A number above the bound that is not 5 or 6 modulo 7 is not placed. -/
lemma not_mem_of_mod (U : Finset ℕ) (M n k : ℕ) (hU : Good U M n) (hk : M < k)
    (hmod : k % 7 ≠ 5 ∧ k % 7 ≠ 6) : k ∉ U := by
  rw [hU]
  rintro (h | ⟨i, hi1, -, hi⟩)
  · omega
  · have := dl_range i hi1
    unfold Cc at hi
    omega

/-- A placed number in the range of the block of index t (above the bound) is Cc t. -/
lemma only (U : Finset ℕ) (M n t k : ℕ) (hU : Good U M n) (hk : M < k)
    (h1 : 7 * t - 7 < k) (h2 : k ≤ 7 * t) (ht : 1 ≤ t) (hmem : k ∈ U) : k = Cc t := by
  rcases (hU k).mp hmem with h | ⟨i, hi1, -, hki⟩
  · omega
  · have := dl_range i hi1
    have hij : i = t := by unfold Cc at hki; omega
    rw [hki, hij]

lemma low (U : Finset ℕ) (M n : ℕ) (hU : Good U M n) : ∀ k, 0 < k → k ≤ M → k ∈ U :=
  fun k hk hle => (hU k).mpr (Or.inl ⟨hk, hle⟩)

lemma inv (J : ℕ) : Inv (3 * J) (14 * J) ∧ Inv (3 * J + 1) (14 * J + 4) ∧
    Inv (3 * J + 2) (14 * J + 9) := by
  have s1 : ∀ J, Inv (3 * J) (14 * J) → Inv (3 * J + 1) (14 * J + 4) := by
    intro J h
    apply gen_step (3 * J) (14 * J) (14 * J + 4) (14 * J + 1) (14 * J + 2) (14 * J + 3)
      (14 * J + 4) h
    · intro U hU
      refine ⟨by omega, ⟨not_mem_of_mod U _ _ _ hU (by omega) (by omega),
        not_mem_of_mod U _ _ _ hU (by omega) (by omega),
        not_mem_of_mod U _ _ _ hU (by omega) (by omega),
        not_mem_of_mod U _ _ _ hU (by omega) (by omega)⟩,
        fun k hk hlt => low U _ _ hU k hk (by omega), fun k h1 h2 => by omega,
        fun k h1 h2 => by omega, fun k h1 h2 => by omega, fun k h1 h2 => by omega⟩
    · rw [show 2 * (3 * J) + 1 = 3 * (2 * J) + 1 by ring, Af1]; ring
    · rw [show 2 * (3 * J) + 2 = 3 * (2 * J) + 2 by ring, Af2]; ring
    · unfold Cc; rw [dl1, Af1]; omega
    · omega
    · omega
  have s2 : ∀ J, Inv (3 * J + 1) (14 * J + 4) → Inv (3 * J + 2) (14 * J + 9) := by
    intro J h
    have hr := dl_range (2 * J + 1) (by omega)
    have hC : Cc (2 * J + 1) = 7 * (2 * J + 1) - dl (2 * J + 1) := rfl
    have hD : Cc (3 * J + 1 + 1) = Af (3 * J + 1 + 1) + (14 * J + 9) := by
      rw [show 3 * J + 1 + 1 = 3 * J + 2 by ring]
      unfold Cc; rw [dl2, Af2]; omega
    have hAy : Af (2 * (3 * J + 1) + 2) = 14 * J + 8 := by
      rw [show 2 * (3 * J + 1) + 2 = 3 * (2 * J + 1) + 1 by ring, Af1]; ring
    have hAw : Af (2 * (3 * J + 1) + 1) = 14 * J + 4 + dl (2 * J + 1) := by
      rw [show 2 * (3 * J + 1) + 1 = 3 * (2 * J) + 3 by ring, Af3]; ring
    rcases hr with h0 | h0
    · -- Cc (2 J + 1) = 14 J + 6
      apply gen_step (3 * J + 1) (14 * J + 4) (14 * J + 9) (14 * J + 5) (14 * J + 7) (14 * J + 8)
        (14 * J + 9) h
      · intro U hU
        have hCmem : Cc (2 * J + 1) ∈ U := (hU _).mpr (Or.inr ⟨2 * J + 1, by omega, by omega, rfl⟩)
        refine ⟨by omega, ⟨fun hm => by
            have := only U _ _ (2 * J + 1) _ hU (by omega) (by omega) (by omega) (by omega) hm
            omega,
          not_mem_of_mod U _ _ _ hU (by omega) (by omega),
          not_mem_of_mod U _ _ _ hU (by omega) (by omega),
          not_mem_of_mod U _ _ _ hU (by omega) (by omega)⟩,
          fun k hk hlt => low U _ _ hU k hk (by omega),
          fun k h1 h2 => by rw [show k = Cc (2 * J + 1) by omega]; exact hCmem,
          fun k h1 h2 => by omega, fun k h1 h2 => by omega, fun k h1 h2 => ?_⟩
        rcases Nat.lt_trichotomy k (14 * J + 6) with h' | h' | h'
        · omega
        · right; right; right; right; rw [show k = Cc (2 * J + 1) by omega]; exact hCmem
        · omega
      · rw [hAw]; omega
      · exact hAy
      · exact hD
      · omega
      · omega
    · -- Cc (2 J + 1) = 14 J + 5
      apply gen_step (3 * J + 1) (14 * J + 4) (14 * J + 9) (14 * J + 6) (14 * J + 7) (14 * J + 8)
        (14 * J + 9) h
      · intro U hU
        have hCmem : Cc (2 * J + 1) ∈ U := (hU _).mpr (Or.inr ⟨2 * J + 1, by omega, by omega, rfl⟩)
        refine ⟨by omega, ⟨fun hm => by
            have := only U _ _ (2 * J + 1) _ hU (by omega) (by omega) (by omega) (by omega) hm
            omega,
          not_mem_of_mod U _ _ _ hU (by omega) (by omega),
          not_mem_of_mod U _ _ _ hU (by omega) (by omega),
          not_mem_of_mod U _ _ _ hU (by omega) (by omega)⟩,
          fun k hk hlt => ?_,
          fun k h1 h2 => by omega,
          fun k h1 h2 => by omega, fun k h1 h2 => by omega, fun k h1 h2 => ?_⟩
        · rcases Nat.lt_or_ge k (14 * J + 5) with h' | h'
          · exact low U _ _ hU k hk (by omega)
          · rw [show k = Cc (2 * J + 1) by omega]; exact hCmem
        · rcases Nat.lt_or_ge k (14 * J + 6) with h' | h'
          · right; right; right; right; rw [show k = Cc (2 * J + 1) by omega]; exact hCmem
          · omega
      · rw [hAw]; omega
      · exact hAy
      · exact hD
      · omega
      · omega
  have s3 : ∀ J, Inv (3 * J + 2) (14 * J + 9) → Inv (3 * (J + 1)) (14 * (J + 1)) := by
    intro J h
    have hr := dl_range (2 * J + 2) (by omega)
    have hr' := dl_range (J + 1) (by omega)
    have hC : Cc (2 * J + 2) = 7 * (2 * J + 2) - dl (2 * J + 2) := rfl
    have hD : Cc (3 * J + 2 + 1) = Af (3 * J + 2 + 1) + (14 * J + 14) := by
      rw [show 3 * J + 2 + 1 = 3 * J + 3 by ring]
      unfold Cc; rw [dl3, Af3]; omega
    have hAw : Af (2 * (3 * J + 2) + 1) = 14 * J + 10 := by
      rw [show 2 * (3 * J + 2) + 1 = 3 * (2 * J + 1) + 2 by ring, Af2]; ring
    have hAy : Af (2 * (3 * J + 2) + 2) = 14 * J + 11 + dl (2 * J + 2) := by
      rw [show 2 * (3 * J + 2) + 2 = 3 * (2 * J + 1) + 3 by ring, Af3]; ring
    rw [show 3 * (J + 1) = 3 * J + 2 + 1 by ring, show 14 * (J + 1) = 14 * J + 14 by ring]
    rcases hr with h0 | h0
    · -- Cc (2 J + 2) = 14 J + 13
      apply gen_step (3 * J + 2) (14 * J + 9) (14 * J + 14) (14 * J + 10) (14 * J + 11)
        (14 * J + 12) (14 * J + 14) h
      · intro U hU
        have hCmem : Cc (2 * J + 2) ∈ U := (hU _).mpr (Or.inr ⟨2 * J + 2, by omega, by omega, rfl⟩)
        refine ⟨by omega, ⟨not_mem_of_mod U _ _ _ hU (by omega) (by omega),
          not_mem_of_mod U _ _ _ hU (by omega) (by omega),
          fun hm => by
            have := only U _ _ (2 * J + 2) _ hU (by omega) (by omega) (by omega) (by omega) hm
            omega,
          not_mem_of_mod U _ _ _ hU (by omega) (by omega)⟩,
          fun k hk hlt => low U _ _ hU k hk (by omega),
          fun k h1 h2 => by omega, fun k h1 h2 => by omega,
          fun k h1 h2 => by rw [show k = Cc (2 * J + 2) by omega]; exact hCmem,
          fun k h1 h2 => ?_⟩
        rcases Nat.lt_trichotomy k (14 * J + 13) with h' | h' | h'
        · omega
        · right; right; right; right; rw [show k = Cc (2 * J + 2) by omega]; exact hCmem
        · omega
      · exact hAw
      · rw [hAy]; omega
      · exact hD
      · omega
      · omega
    · -- Cc (2 J + 2) = 14 J + 12
      apply gen_step (3 * J + 2) (14 * J + 9) (14 * J + 14) (14 * J + 10) (14 * J + 11)
        (14 * J + 13) (14 * J + 14) h
      · intro U hU
        have hCmem : Cc (2 * J + 2) ∈ U := (hU _).mpr (Or.inr ⟨2 * J + 2, by omega, by omega, rfl⟩)
        refine ⟨by omega, ⟨not_mem_of_mod U _ _ _ hU (by omega) (by omega),
          not_mem_of_mod U _ _ _ hU (by omega) (by omega),
          fun hm => by
            have := only U _ _ (2 * J + 2) _ hU (by omega) (by omega) (by omega) (by omega) hm
            omega,
          not_mem_of_mod U _ _ _ hU (by omega) (by omega)⟩,
          fun k hk hlt => low U _ _ hU k hk (by omega),
          fun k h1 h2 => by omega,
          fun k h1 h2 => by rw [show k = Cc (2 * J + 2) by omega]; exact hCmem,
          fun k h1 h2 => by omega,
          fun k h1 h2 => ?_⟩
        rcases Nat.lt_trichotomy k (14 * J + 12) with h' | h' | h'
        · omega
        · right; right; right; right; rw [show k = Cc (2 * J + 2) by omega]; exact hCmem
        · omega
      · exact hAw
      · rw [hAy]; omega
      · exact hD
      · omega
      · omega
  induction J with
  | zero =>
    have h0 : Inv (3 * 0) (14 * 0) := by
      refine ⟨fun _ => 0, fun _ => 0, ∅, ?_, ?_, ?_⟩
      · have : Cc 0 = 0 := by unfold Cc; simp
        rw [Nat.mul_zero, this, state]
      · intro k
        simp only [Finset.notMem_empty, false_iff]
        rintro (h | ⟨i, h1, h2, -⟩) <;> omega
      · intro m h1 h2; omega
    exact ⟨h0, s1 0 h0, s2 0 (s1 0 h0)⟩
  | succ J ih =>
    have h3 := s3 J ih.2.2
    exact ⟨h3, s1 (J + 1) h3, s2 (J + 1) (s1 (J + 1) h3)⟩

lemma c_eq (n : ℕ) : c n = Cc n := by
  obtain ⟨J, hJ⟩ : ∃ J, n = 3 * J ∨ n = 3 * J + 1 ∨ n = 3 * J + 2 := ⟨n / 3, by omega⟩
  obtain ⟨⟨α, β, U, h0, -⟩, ⟨α1, β1, U1, h1, -⟩, ⟨α2, β2, U2, h2, -⟩⟩ := inv J
  unfold c
  rcases hJ with rfl | rfl | rfl
  · rw [h0]
  · rw [h1]
  · rw [h2]

theorem main' : ∀ n : ℕ, 1 ≤ n → c n + 1 = 7 * n ∨ c n + 2 = 7 * n := by
  intro n hn
  rw [c_eq]
  have := dl_range n hn
  unfold Cc
  omega

end OMA.A326663

theorem OMA.solution : type_of% @OMA.S_oeis_a326663.main :=
  OMA.A326663.main'
