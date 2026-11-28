import OMAStatements.S_oeis_a003278

open OMA.S_oeis_a003278

namespace OMA.P_oeis_a003278

lemma nth_image {P Q : ℕ → Prop} (g : ℕ → ℕ) (hg : StrictMono g)
    (hQ : ∀ y, Q y ↔ ∃ x, P x ∧ y = g x) (hP : (setOf P).Infinite) (i : ℕ) :
    Nat.nth Q i = g (Nat.nth P i) := by
  classical
  have hPx : P (Nat.nth P i) := Nat.nth_mem_of_infinite hP i
  have hcP : Nat.count P (Nat.nth P i) = i := Nat.count_nth_of_infinite hP i
  have hQx : Q (g (Nat.nth P i)) := (hQ _).2 ⟨Nat.nth P i, hPx, rfl⟩
  have hcount : Nat.count Q (g (Nat.nth P i)) = Nat.count P (Nat.nth P i) := by
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    have hset : (Finset.range (g (Nat.nth P i))).filter Q =
        ((Finset.range (Nat.nth P i)).filter P).image g := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hy, hq⟩
        obtain ⟨x, hx, rfl⟩ := (hQ y).1 hq
        exact ⟨x, ⟨hg.lt_iff_lt.1 hy, hx⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hpx⟩, rfl⟩
        exact ⟨hg hx, (hQ _).2 ⟨x, hpx, rfl⟩⟩
    rw [hset, Finset.card_image_of_injective _ hg.injective]
  calc Nat.nth Q i = Nat.nth Q (Nat.count Q (g (Nat.nth P i))) := by rw [hcount, hcP]
    _ = g (Nat.nth P i) := Nat.nth_count hQx

lemma gen_of_digits {d : ℕ} (h : Digits01 d) : Generated (3 * d + 1) := by
  induction h with
  | zero => exact Generated.seed
  | @append0 x hx ih =>
    have e : 3 * (3 * x) + 1 = 3 * (3 * x + 1) - 2 := by omega
    rw [e]
    exact Generated.low ih
  | @append1 x hx ih =>
    exact Generated.high ih

lemma digits_of_gen {y : ℕ} (h : Generated y) : ∃ d, Digits01 d ∧ y = 3 * d + 1 := by
  induction h with
  | seed => exact ⟨0, Digits01.zero, rfl⟩
  | @low x hx ih =>
    obtain ⟨d, hd, rfl⟩ := ih
    exact ⟨3 * d, Digits01.append0 hd, by omega⟩
  | @high x hx ih =>
    obtain ⟨d, hd, rfl⟩ := ih
    exact ⟨3 * d + 1, Digits01.append1 hd, by omega⟩

lemma gen_iff : ∀ y, Generated y ↔ ∃ x, Digits01 x ∧ y = 3 * x + 1 := by
  intro y
  constructor
  · exact digits_of_gen
  · rintro ⟨d, hd, rfl⟩
    exact gen_of_digits hd

lemma cp_of_digits {d : ℕ} (h : Digits01 d) : CantorParent (2 * d) := by
  induction h with
  | zero => exact CantorParent.root
  | @append0 x hx ih =>
    have e : 2 * (3 * x) = 3 * (2 * x) := by ring
    rw [e]
    exact CantorParent.left ih
  | @append1 x hx ih =>
    have e : 2 * (3 * x + 1) = 3 * (2 * x) + 2 := by ring
    rw [e]
    exact CantorParent.right ih

lemma digits_of_cp {p : ℕ} (h : CantorParent p) : ∃ d, Digits01 d ∧ p = 2 * d := by
  induction h with
  | root => exact ⟨0, Digits01.zero, rfl⟩
  | @left p hp ih =>
    obtain ⟨d, hd, rfl⟩ := ih
    exact ⟨3 * d, Digits01.append0 hd, by ring⟩
  | @right p hp ih =>
    obtain ⟨d, hd, rfl⟩ := ih
    exact ⟨3 * d + 1, Digits01.append1 hd, by ring⟩

lemma gap_iff : ∀ y, gap y ↔ ∃ x, Digits01 x ∧ y = 6 * x + 1 := by
  intro y
  unfold gap
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨d, hd, rfl⟩ := digits_of_cp hp
    exact ⟨d, hd, by ring⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨2 * d, cp_of_digits hd, by ring⟩

lemma digits_pow (k : ℕ) : Digits01 (3 ^ k) := by
  induction k with
  | zero => exact Digits01.append1 Digits01.zero
  | succ k ih =>
    rw [pow_succ, mul_comm]
    exact Digits01.append0 ih

lemma lt_three_pow (B : ℕ) : B < 3 ^ B := by
  induction B with
  | zero => norm_num
  | succ B ih => rw [pow_succ]; omega

lemma digits_infinite : (setOf Digits01).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have h1 : 3 ^ B ≤ B := hB (digits_pow B)
  have h2 := lt_three_pow B
  omega

end OMA.P_oeis_a003278

open OMA.P_oeis_a003278 in
theorem OMA.solution : type_of% @OMA.S_oeis_a003278.main := by
  intro i
  show Nat.nth Generated i + 2 = 3 * (Nat.nth Digits01 i + 1) ∧
    Nat.nth gap i + 5 = 6 * (Nat.nth Digits01 i + 1)
  have h1 : Nat.nth Generated i = 3 * Nat.nth Digits01 i + 1 :=
    nth_image (fun d => 3 * d + 1) (by intro a b h; show 3 * a + 1 < 3 * b + 1; omega) gen_iff
      digits_infinite i
  have h2 : Nat.nth gap i = 6 * Nat.nth Digits01 i + 1 :=
    nth_image (fun d => 6 * d + 1) (by intro a b h; show 6 * a + 1 < 6 * b + 1; omega) gap_iff
      digits_infinite i
  constructor <;> omega
