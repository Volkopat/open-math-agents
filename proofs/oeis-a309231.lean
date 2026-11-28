import OMAStatements.S_oeis_a309231
import Mathlib

-- Problem: OEIS A309231, conjecture of Kimberling: for the solution of the complementary
-- equation c(n) = a(2n) + b(2n) (a and b least new), 9n - c(n) is 1 or 2 for each n >= 1.
-- Statement: statements/oeis-a309231.lean (declaration OMA.S_oeis_a309231.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let dl(2j+1) = 2 and dl(2j) = 3 - dl(j), so dl is 1 or 2, and let Cc(n) = 9n - dl(n).
-- Invariant: after step 2j the placed numbers are {1, ..., 9j} and the Cc(i), 1 <= i <= 2j,
-- and c(i) = Cc(i). The numbers Cc(i) are 7 or 8 modulo 9. Step 2j+1 places 9j + 1, ...,
-- 9j + 4, and c = (9j + 3) + (9j + 4) = 9(2j+1) - 2. In 9j + 5, ..., 9j + 9 the only placed
-- number is Cc(j+1) (9j + 7 or 9j + 8), so step 2j+2 places the four other numbers, and
-- c is 18j + 17 or 18j + 16, which is 9(2j+2) - (3 - dl(j+1)).

namespace OMA.A309231

open OMA.S_oeis_a309231

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

/-- The correction term: c(n) = 9 n - dl(n). -/
def dl : ℕ → ℕ
  | n => if h : n = 0 then 0 else if h' : n % 2 = 1 then 2 else 3 - dl (n / 2)
decreasing_by omega

lemma dl_odd (j : ℕ) : dl (2 * j + 1) = 2 := by
  rw [dl, dif_neg (by omega), dif_pos (by omega)]

lemma dl_even (j : ℕ) (hj : 1 ≤ j) : dl (2 * j) = 3 - dl j := by
  rw [dl, dif_neg (by omega), dif_neg (by omega), show 2 * j / 2 = j by omega]

lemma dl_range : ∀ n : ℕ, 1 ≤ n → dl n = 1 ∨ dl n = 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
    · have := ih j (by omega) (by omega)
      rw [dl_even j (by omega)]; omega
    · rw [dl_odd]; right; rfl

/-- The closed form of c. -/
def Cc (n : ℕ) : ℕ := 9 * n - dl n

lemma state_succ (n : ℕ) (a1 b1 a2 b2 c0 : ℕ) (U : Finset ℕ)
    (h : state n = (a1, b1, a2, b2, c0, U)) (w x y z : ℕ)
    (m : leastNew U = w ∧ leastNew (insert w U) = x ∧ leastNew (insert x (insert w U)) = y ∧
      leastNew (insert y (insert x (insert w U))) = z) :
    state (n + 1) = (w, x, y, z, y + z,
      insert (y + z) (insert z (insert y (insert x (insert w U))))) := by
  obtain ⟨m1, m2, m3, m4⟩ := m
  rw [state, h]
  simp only [m1, m2, m3, m4]

/-- The placed set: the numbers up to M and the numbers Cc i with 1 <= i <= n. -/
def Good (U : Finset ℕ) (M n : ℕ) : Prop :=
  ∀ k, k ∈ U ↔ (1 ≤ k ∧ k ≤ M) ∨ ∃ i, 1 ≤ i ∧ i ≤ n ∧ k = Cc i

lemma gen_step (n M M' w x y z : ℕ) (a1 b1 a2 b2 c0 : ℕ) (U : Finset ℕ)
    (hst : state n = (a1, b1, a2, b2, c0, U)) (hU : Good U M n)
    (hw : 0 < w) (hwx : w < x) (hxy : x < y) (hyz : y < z)
    (hwU : w ∉ U) (hxU : x ∉ U) (hyU : y ∉ U) (hzU : z ∉ U)
    (h1 : ∀ k, 0 < k → k < w → k ∈ U) (h2 : ∀ k, w < k → k < x → k ∈ U)
    (h3 : ∀ k, x < k → k < y → k ∈ U) (h4 : ∀ k, y < k → k < z → k ∈ U)
    (hD : Cc (n + 1) = y + z) (hM : M ≤ M') (hzM : z ≤ M')
    (hfill : ∀ k, M < k → k ≤ M' → k = w ∨ k = x ∨ k = y ∨ k = z ∨ k ∈ U) :
    ∃ U', state (n + 1) = (w, x, y, z, Cc (n + 1), U') ∧ Good U' M' (n + 1) := by
  have h := state_succ n _ _ _ _ _ U hst w x y z
    (four_mex U w x y z hw hwx hxy hyz hwU hxU hyU hzU h1 h2 h3 h4)
  refine ⟨_, by rw [h, hD], ?_⟩
  intro k
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_insert, hU]
  constructor
  · rintro (h | h | h | h | h | ⟨h, h'⟩ | ⟨i, hi1, hi, hk⟩)
    · right; exact ⟨n + 1, by omega, le_rfl, by rw [hD, h]⟩
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
      · left; rw [hk, show i = n + 1 by omega, hD]

/-- A number above the bound that is not 7 or 8 modulo 9 is not placed. -/
lemma not_mem_of_mod (U : Finset ℕ) (M n k : ℕ) (hU : Good U M n) (hk : M < k)
    (hmod : k % 9 ≠ 7 ∧ k % 9 ≠ 8) : k ∉ U := by
  rw [hU]
  rintro (h | ⟨i, hi1, -, hi⟩)
  · omega
  · have := dl_range i hi1
    unfold Cc at hi
    omega

lemma inv (j : ℕ) : ∃ w x y z U, state (2 * j) = (w, x, y, z, Cc (2 * j), U) ∧
    Good U (9 * j) (2 * j) := by
  induction j with
  | zero =>
    refine ⟨0, 0, 0, 0, ∅, ?_, ?_⟩
    · have : Cc 0 = 0 := by unfold Cc; simp
      rw [Nat.mul_zero, this, state]
    · intro k
      simp only [Finset.notMem_empty, false_iff]
      rintro (h | ⟨i, h1, h2, -⟩) <;> omega
  | succ j ih =>
    obtain ⟨w0, x0, y0, z0, U, hst, hU⟩ := ih
    -- step 2 j + 1 places 9 j + 1, ..., 9 j + 4
    have low : ∀ k, 0 < k → k < 9 * j + 1 → k ∈ U := by
      intro k hk hlt; exact (hU k).mpr (Or.inl ⟨hk, by omega⟩)
    obtain ⟨U1, hst1, hU1⟩ := gen_step (2 * j) (9 * j) (9 * j + 4)
      (9 * j + 1) (9 * j + 2) (9 * j + 3) (9 * j + 4) _ _ _ _ _ U hst hU
      (by omega) (by omega) (by omega) (by omega)
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      low (fun k h1 h2 => by omega) (fun k h1 h2 => by omega) (fun k h1 h2 => by omega)
      (by unfold Cc; rw [dl_odd]; omega) (by omega) (by omega) (fun k h1 h2 => by omega)
    -- step 2 j + 2 places the four numbers of 9 j + 5, ..., 9 j + 9 that are not c(j + 1)
    have hr := dl_range (j + 1) (by omega)
    have hCj : Cc (j + 1) = 9 * (j + 1) - dl (j + 1) := rfl
    have hCmem : Cc (j + 1) ∈ U1 := (hU1 _).mpr (Or.inr ⟨j + 1, by omega, by omega, rfl⟩)
    have only : ∀ k, 9 * j + 4 < k → k ≤ 9 * j + 9 → k ∈ U1 → k = Cc (j + 1) := by
      intro k hk1 hk2 hk
      rcases (hU1 k).mp hk with h | ⟨i, hi1, hi, hki⟩
      · omega
      · have := dl_range i hi1
        have hij : i = j + 1 := by unfold Cc at hki; omega
        rw [hki, hij]
    have low1 : ∀ k, 0 < k → k < 9 * j + 5 → k ∈ U1 := by
      intro k hk hlt; exact (hU1 k).mpr (Or.inl ⟨hk, by omega⟩)
    have h5 : 9 * j + 5 ∉ U1 := not_mem_of_mod U1 _ _ _ hU1 (by omega) (by omega)
    have h6 : 9 * j + 6 ∉ U1 := not_mem_of_mod U1 _ _ _ hU1 (by omega) (by omega)
    have h9 : 9 * j + 9 ∉ U1 := not_mem_of_mod U1 _ _ _ hU1 (by omega) (by omega)
    have hde := dl_even (j + 1) (by omega)
    rcases hr with h0 | h0
    · -- c(j + 1) = 9 j + 8
      obtain ⟨U2, hst2, hU2⟩ := gen_step (2 * j + 1) (9 * j + 4) (9 * j + 9)
        (9 * j + 5) (9 * j + 6) (9 * j + 7) (9 * j + 9) _ _ _ _ _ U1 hst1 hU1
        (by omega) (by omega) (by omega) (by omega) h5 h6
        (fun h => by have := only _ (by omega) (by omega) h; omega) h9
        low1 (fun k h1 h2 => by omega) (fun k h1 h2 => by omega)
        (fun k h1 h2 => by rw [show k = Cc (j + 1) by omega]; exact hCmem)
        (by unfold Cc; rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, hde]; omega)
        (by omega) (by omega)
        (fun k h1 h2 => by
          rcases Nat.lt_trichotomy k (9 * j + 8) with h | h | h
          · omega
          · right; right; right; right
            rw [show k = Cc (j + 1) by omega]; exact hCmem
          · omega)
      exact ⟨_, _, _, _, U2, hst2, by
        rw [show 9 * (j + 1) = 9 * j + 9 by ring]; exact hU2⟩
    · -- c(j + 1) = 9 j + 7
      obtain ⟨U2, hst2, hU2⟩ := gen_step (2 * j + 1) (9 * j + 4) (9 * j + 9)
        (9 * j + 5) (9 * j + 6) (9 * j + 8) (9 * j + 9) _ _ _ _ _ U1 hst1 hU1
        (by omega) (by omega) (by omega) (by omega) h5 h6
        (fun h => by have := only _ (by omega) (by omega) h; omega) h9
        low1 (fun k h1 h2 => by omega)
        (fun k h1 h2 => by rw [show k = Cc (j + 1) by omega]; exact hCmem)
        (fun k h1 h2 => by omega)
        (by unfold Cc; rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, hde]; omega)
        (by omega) (by omega)
        (fun k h1 h2 => by
          rcases Nat.lt_trichotomy k (9 * j + 7) with h | h | h
          · omega
          · right; right; right; right
            rw [show k = Cc (j + 1) by omega]; exact hCmem
          · omega)
      exact ⟨_, _, _, _, U2, hst2, by
        rw [show 9 * (j + 1) = 9 * j + 9 by ring]; exact hU2⟩

/-- c(n) = Cc(n) for each n. -/
lemma c_eq (n : ℕ) : c n = Cc n := by
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · obtain ⟨w, x, y, z, U, hst, -⟩ := inv j
    unfold c; rw [hst]
  · obtain ⟨w0, x0, y0, z0, U, hst, hU⟩ := inv j
    have low : ∀ k, 0 < k → k < 9 * j + 1 → k ∈ U := by
      intro k hk hlt; exact (hU k).mpr (Or.inl ⟨hk, by omega⟩)
    obtain ⟨U1, hst1, -⟩ := gen_step (2 * j) (9 * j) (9 * j + 4)
      (9 * j + 1) (9 * j + 2) (9 * j + 3) (9 * j + 4) _ _ _ _ _ U hst hU
      (by omega) (by omega) (by omega) (by omega)
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      low (fun k h1 h2 => by omega) (fun k h1 h2 => by omega) (fun k h1 h2 => by omega)
      (by unfold Cc; rw [dl_odd]; omega) (by omega) (by omega) (fun k h1 h2 => by omega)
    unfold c; rw [hst1]

theorem main' : ∀ n : ℕ, 1 ≤ n → c n + 1 = 9 * n ∨ c n + 2 = 9 * n := by
  intro n hn
  rw [c_eq]
  have := dl_range n hn
  unfold Cc
  omega

end OMA.A309231

theorem OMA.solution : type_of% @OMA.S_oeis_a309231.main :=
  OMA.A309231.main'
