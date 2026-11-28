import OMAStatements.S_oeis_a236043
import Mathlib

namespace OMA.P236043
open OMA.S_oeis_a236043

/-- The m-th triangular number. -/
def tri (m : ℕ) : ℕ := m * (m + 1) / 2

lemma tri_succ (m : ℕ) : tri (m + 1) = tri m + (m + 1) := by
  unfold tri
  have h : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) := by ring
  rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

lemma tri_strictMono : StrictMono tri :=
  strictMono_nat_of_lt_succ (fun m => by rw [tri_succ]; omega)

lemma ncard_le_of (S : Set ℕ) (hS : ∀ t ∈ S, ∃ m, t = tri m) (B : ℕ)
    (h : ∀ m, tri m ∈ S → m < B) : S.ncard ≤ B := by
  have hsub : S ⊆ (((Finset.range B).image tri : Finset ℕ) : Set ℕ) := by
    intro t ht
    obtain ⟨m, rfl⟩ := hS t ht
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨m, h m ht, rfl⟩
  calc S.ncard ≤ (((Finset.range B).image tri : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ((Finset.range B).image tri).card := Set.ncard_coe_finset _
    _ ≤ (Finset.range B).card := Finset.card_image_le
    _ = B := Finset.card_range B

lemma le_ncard_of (S : Set ℕ) (hfin : S.Finite) (A : ℕ) (h : ∀ m < A, tri m ∈ S) :
    A ≤ S.ncard := by
  have hsub : (((Finset.range A).image tri : Finset ℕ) : Set ℕ) ⊆ S := by
    intro t ht
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at ht
    obtain ⟨m, hm, rfl⟩ := ht
    exact h m hm
  calc A = (Finset.range A).card := (Finset.card_range A).symm
    _ = ((Finset.range A).image tri).card :=
        (Finset.card_image_of_injective _ tri_strictMono.injective).symm
    _ = (((Finset.range A).image tri : Finset ℕ) : Set ℕ).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ S.ncard := Set.ncard_le_ncard hsub hfin

lemma triLe_finite (N : ℕ) : (triLe N).Finite :=
  (Set.finite_Iic N).subset (fun _ ht => ht.1)

lemma triLt_finite (N : ℕ) : (triLt N).Finite :=
  (Set.finite_Iio N).subset (fun _ ht => ht.1)

lemma le_a' (N A : ℕ) (hA : tri A ≤ N) : A + 1 ≤ (triLe N).ncard :=
  le_ncard_of _ (triLe_finite N) (A + 1) (fun m hm =>
    ⟨le_trans (tri_strictMono.monotone (by omega)) hA, ⟨m, rfl⟩⟩)

lemma le_b' (N A : ℕ) (hA : tri A < N) : A + 1 ≤ (triLt N).ncard :=
  le_ncard_of _ (triLt_finite N) (A + 1) (fun m hm =>
    ⟨lt_of_le_of_lt (tri_strictMono.monotone (by omega)) hA, ⟨m, rfl⟩⟩)

lemma a_le' (N B : ℕ) (hB : N < tri B) : (triLe N).ncard ≤ B :=
  ncard_le_of _ (fun _ ht => ht.2) B (fun m hm => by
    by_contra hc
    have := tri_strictMono.monotone (show B ≤ m by omega)
    exact absurd hm.1 (by omega))

lemma b_le' (N B : ℕ) (hB : N ≤ tri B) : (triLt N).ncard ≤ B :=
  ncard_le_of _ (fun _ ht => ht.2) B (fun m hm => by
    by_contra hc
    have := tri_strictMono.monotone (show B ≤ m by omega)
    exact absurd hm.1 (by omega))

lemma b_le_a (N : ℕ) : (triLt N).ncard ≤ (triLe N).ncard :=
  Set.ncard_le_ncard (fun _ ht => ⟨le_of_lt ht.1, ht.2⟩) (triLe_finite N)

lemma beginsWith_of (d : ℕ) (hd1 : 1 ≤ d) (hd : d < 10) :
    ∀ k x : ℕ, d * 10 ^ k ≤ x → x < (d + 1) * 10 ^ k → beginsWith x d := by
  intro k
  induction k with
  | zero =>
    intro x h1 h2
    have hx : x = d := by simp at h1 h2; omega
    subst hx
    unfold beginsWith
    rw [Nat.digits_of_lt 10 x (by omega) hd]
    rfl
  | succ k ih =>
    intro x h1 h2
    have hpos : 0 < x := by
      have : 0 < 10 ^ (k + 1) := by positivity
      nlinarith
    have h1' : d * 10 ^ k ≤ x / 10 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      calc d * 10 ^ k * 10 = d * 10 ^ (k + 1) := by ring
        _ ≤ x := h1
    have h2' : x / 10 < (d + 1) * 10 ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      calc x < (d + 1) * 10 ^ (k + 1) := h2
        _ = (d + 1) * 10 ^ k * 10 := by ring
    have ih' := ih (x / 10) h1' h2'
    unfold beginsWith at ih' ⊢
    rw [Nat.digits_def' (by norm_num) hpos, List.getLast?_cons, ih']
    rfl

lemma key (n : ℕ) (hn : 1 ≤ n) (hn1 : n ≠ 1) :
    ∃ d k : ℕ, (d = 4 ∨ d = 1) ∧ d * 10 ^ k ≤ b n ∧ a n < (d + 1) * 10 ^ k := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hk : 1 ≤ k := by omega
    have hP : 10 ≤ 10 ^ k := by
      calc 10 = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    obtain ⟨Q, hQ⟩ : ∃ Q, 10 ^ k = Q + 1 := ⟨10 ^ k - 1, by omega⟩
    have hQ1 : 9 ≤ Q := by omega
    have hN : 10 ^ (2 * k) = (Q + 1) * (Q + 1) := by rw [two_mul, pow_add, hQ]
    refine ⟨1, k, Or.inr rfl, ?_, ?_⟩
    · have h := le_b' (10 ^ (2 * k)) Q (by
        rw [hN]; unfold tri; rw [Nat.div_lt_iff_lt_mul (by norm_num)]; nlinarith)
      have hb : Q + 1 ≤ b (2 * k) := h
      rw [hQ]; omega
    · have h := a_le' (10 ^ (2 * k)) (2 * Q + 1) (by
        rw [hN]; unfold tri
        rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by norm_num)]; nlinarith)
      have ha : a (2 * k) ≤ 2 * Q + 1 := h
      rw [hQ]; omega
  · have hk : 1 ≤ k := by omega
    have hP : 10 ≤ 10 ^ k := by
      calc 10 = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    obtain ⟨Q, hQ⟩ : ∃ Q, 10 ^ k = Q + 1 := ⟨10 ^ k - 1, by omega⟩
    have hQ1 : 9 ≤ Q := by omega
    have hN : 10 ^ (2 * k + 1) = 10 * ((Q + 1) * (Q + 1)) := by
      rw [pow_succ, two_mul, pow_add, hQ]; ring
    refine ⟨4, k, Or.inl rfl, ?_, ?_⟩
    · have h := le_b' (10 ^ (2 * k + 1)) (4 * Q + 3) (by
        rw [hN]; unfold tri; rw [Nat.div_lt_iff_lt_mul (by norm_num)]; nlinarith)
      have hb : 4 * Q + 3 + 1 ≤ b (2 * k + 1) := h
      rw [hQ]; omega
    · have h := a_le' (10 ^ (2 * k + 1)) (5 * Q + 4) (by
        rw [hN]; unfold tri
        rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by norm_num)]; nlinarith)
      have ha : a (2 * k + 1) ≤ 5 * Q + 4 := h
      rw [hQ]; omega

lemma a_one : a 1 = 5 := by
  have h1 : 4 + 1 ≤ a 1 := le_a' (10 ^ 1) 4 (by decide)
  have h2 : a 1 ≤ 5 := a_le' (10 ^ 1) 5 (by decide)
  omega

lemma b_one : b 1 = 4 := by
  have h1 : 3 + 1 ≤ b 1 := le_b' (10 ^ 1) 3 (by decide)
  have h2 : b 1 ≤ 4 := b_le' (10 ^ 1) 4 (by decide)
  omega

theorem sol : type_of% @OMA.S_oeis_a236043.main := by
  have hba : ∀ n, b n ≤ a n := fun n => b_le_a (10 ^ n)
  refine ⟨?_, ⟨a_one, b_one⟩, ?_⟩
  · intro n hn h5
    have hn1 : n ≠ 1 := by
      rintro rfl
      exact h5 a_one
    obtain ⟨d, k, hd, h1, h2⟩ := key n hn hn1
    have hb := hba n
    rcases hd with rfl | rfl
    · exact Or.inl (beginsWith_of 4 (by norm_num) (by norm_num) k (a n) (by omega) h2)
    · exact Or.inr (beginsWith_of 1 (by norm_num) (by norm_num) k (a n) (by omega) h2)
  · intro n hn
    by_cases hn1 : n = 1
    · subst hn1
      rw [b_one]
      exact Or.inl (beginsWith_of 4 (by norm_num) (by norm_num) 0 4 (by norm_num) (by norm_num))
    obtain ⟨d, k, hd, h1, h2⟩ := key n hn hn1
    have hb := hba n
    rcases hd with rfl | rfl
    · exact Or.inl (beginsWith_of 4 (by norm_num) (by norm_num) k (b n) h1 (by omega))
    · exact Or.inr (beginsWith_of 1 (by norm_num) (by norm_num) k (b n) h1 (by omega))

end OMA.P236043

theorem OMA.solution : type_of% @OMA.S_oeis_a236043.main := OMA.P236043.sol
