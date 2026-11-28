import OMAStatements.S_oeis_a288380
import Mathlib

namespace A288380Aux

def E : ℕ → List Bool
  | 0 => []
  | 1 => [false]
  | k + 2 => false :: false :: false :: true :: E k

def Z (k : ℕ) : List Bool := List.replicate k false

open OMA.S_oeis_a288380 in
lemma rw_zeros_one : ∀ (k : ℕ) (w : List Bool),
    rewriteWord (Z k ++ true :: w) = E k ++ true :: false :: rewriteWord w
  | 0, w => by
    show rewriteWord (true :: w) = true :: false :: rewriteWord w
    rw [rewriteWord]
  | 1, w => by
    show rewriteWord (false :: true :: w) = false :: true :: false :: rewriteWord w
    rw [rewriteWord]
  | k + 2, w => by
    have ih := rw_zeros_one k w
    show rewriteWord (false :: false :: (Z k ++ true :: w))
      = false :: false :: false :: true :: (E k ++ true :: false :: rewriteWord w)
    rw [rewriteWord, ih]

open OMA.S_oeis_a288380 in
lemma rw_zeros : ∀ (k : ℕ), rewriteWord (Z k) = E k
  | 0 => by
    show rewriteWord [] = []
    rw [rewriteWord]
  | 1 => by
    show rewriteWord [false] = [false]
    rw [rewriteWord]
  | k + 2 => by
    have ih := rw_zeros k
    show rewriteWord (false :: false :: Z k) = false :: false :: false :: true :: E k
    rw [rewriteWord, ih]

open OMA.S_oeis_a288380 in
def hmap : List Bool → List Bool
  | [] => []
  | _ :: y => true :: false :: rewriteWord y

def good (z : List Bool) : Prop := z = [] ∨ ∃ y, z = true :: y

lemma good_app {u : List Bool} (hu : ∃ y, u = true :: y) (z : List Bool) : good (u ++ z) := by
  obtain ⟨y, rfl⟩ := hu
  exact Or.inr ⟨y ++ z, rfl⟩

lemma good_append {u z : List Bool} (hu : good u) (hz : good z) : good (u ++ z) := by
  rcases hu with rfl | hu
  · exact hz
  · exact good_app hu z

open OMA.S_oeis_a288380 in
lemma h_block (k : ℕ) (z : List Bool) (hz : good z) :
    hmap (true :: (Z k ++ z)) = true :: false :: (E k ++ hmap z) := by
  rcases hz with rfl | ⟨y, rfl⟩
  · show true :: false :: rewriteWord (Z k ++ []) = true :: false :: (E k ++ [])
    rw [List.append_nil, List.append_nil, rw_zeros]
  · show true :: false :: rewriteWord (Z k ++ true :: y)
      = true :: false :: (E k ++ (true :: false :: rewriteWord y))
    rw [rw_zeros_one]

def WP : ℕ → ℕ → List Bool
  | 0, k => true :: Z k
  | n + 1, 0 => WP n 1
  | n + 1, 1 => WP n 2
  | n + 1, 2 => WP n 4 ++ WP n 0
  | n + 1, 3 => WP n 4 ++ WP n 1
  | n + 1, _ + 4 => WP n 4 ++ (WP n 3 ++ WP n 0)

lemma WP0 (n : ℕ) : WP (n + 1) 0 = WP n 1 := rfl
lemma WP1 (n : ℕ) : WP (n + 1) 1 = WP n 2 := rfl
lemma WP2 (n : ℕ) : WP (n + 1) 2 = WP n 4 ++ WP n 0 := rfl
lemma WP3 (n : ℕ) : WP (n + 1) 3 = WP n 4 ++ WP n 1 := rfl
lemma WP4 (n : ℕ) : WP (n + 1) 4 = WP n 4 ++ (WP n 3 ++ WP n 0) := rfl

lemma headW (n : ℕ) : ∀ k : ℕ, k ≤ 4 → ∃ y, WP n k = true :: y := by
  induction n with
  | zero =>
    intro k _
    exact ⟨Z k, rfl⟩
  | succ n ih =>
    intro k hk
    interval_cases k
    · rw [WP0]
      exact ih 1 (by omega)
    · rw [WP1]
      exact ih 2 (by omega)
    · rw [WP2]
      obtain ⟨y, hy⟩ := ih 4 (by omega)
      exact ⟨y ++ WP n 0, by rw [hy]; rfl⟩
    · rw [WP3]
      obtain ⟨y, hy⟩ := ih 4 (by omega)
      exact ⟨y ++ WP n 1, by rw [hy]; rfl⟩
    · rw [WP4]
      obtain ⟨y, hy⟩ := ih 4 (by omega)
      exact ⟨y ++ (WP n 3 ++ WP n 0), by rw [hy]; rfl⟩

lemma hC (n : ℕ) : ∀ k : ℕ, k ≤ 4 → ∀ z : List Bool, good z →
    hmap (WP n k ++ z) = WP (n + 1) k ++ hmap z := by
  induction n with
  | zero =>
    intro k hk z hz
    interval_cases k
    · exact h_block 0 z hz
    · exact h_block 1 z hz
    · exact h_block 2 z hz
    · exact h_block 3 z hz
    · exact h_block 4 z hz
  | succ n ih =>
    intro k hk z hz
    interval_cases k
    · rw [WP0 n, WP0 (n + 1)]
      exact ih 1 (by omega) z hz
    · rw [WP1 n, WP1 (n + 1)]
      exact ih 2 (by omega) z hz
    · rw [WP2 n, WP2 (n + 1)]
      simp only [List.append_assoc]
      rw [ih 4 (by omega) (WP n 0 ++ z) (good_app (headW n 0 (by omega)) z),
        ih 0 (by omega) z hz]
    · rw [WP3 n, WP3 (n + 1)]
      simp only [List.append_assoc]
      rw [ih 4 (by omega) (WP n 1 ++ z) (good_app (headW n 1 (by omega)) z),
        ih 1 (by omega) z hz]
    · rw [WP4 n, WP4 (n + 1)]
      simp only [List.append_assoc]
      rw [ih 4 (by omega) (WP n 3 ++ (WP n 0 ++ z)) (good_app (headW n 3 (by omega)) _),
        ih 3 (by omega) (WP n 0 ++ z) (good_app (headW n 0 (by omega)) z),
        ih 0 (by omega) z hz]

def G : ℕ → ℕ → List Bool
  | _, 0 => []
  | m, n + 1 => WP m 1 ++ G (m + 1) n

lemma good_G (m n : ℕ) : good (G m n) := by
  cases n with
  | zero => exact Or.inl rfl
  | succ n => exact good_app (headW m 1 (by omega)) _

lemma h_G (n : ℕ) : ∀ (m : ℕ) (z : List Bool), good z →
    hmap (G m n ++ z) = G (m + 1) n ++ hmap z := by
  induction n with
  | zero =>
    intro m z _
    rfl
  | succ n ih =>
    intro m z hz
    show hmap ((WP m 1 ++ G (m + 1) n) ++ z) = (WP (m + 1) 1 ++ G (m + 1 + 1) n) ++ hmap z
    simp only [List.append_assoc]
    rw [hC m 1 (by omega) (G (m + 1) n ++ z) (good_append (good_G (m + 1) n) hz),
      ih (m + 1) z hz]

open OMA.S_oeis_a288380 in
def X : ℕ → List Bool
  | 0 => [true]
  | n + 1 => true :: false :: hmap (X n)

lemma X_head (n : ℕ) : ∃ y, X n = true :: y := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ n => exact ⟨false :: hmap (X n), rfl⟩

open OMA.S_oeis_a288380 in
lemma word_succ (n : ℕ) : word (n + 1) = false :: false :: false :: X n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : word (n + 1 + 1) = rewriteWord (word (n + 1)) :=
      Function.iterate_succ_apply' rewriteWord (n + 1) [false, false]
    rw [e, ih]
    obtain ⟨y, hy⟩ := X_head n
    show rewriteWord (false :: false :: false :: X n)
      = false :: false :: false :: true :: false :: hmap (X n)
    rw [hy]
    show rewriteWord (false :: false :: false :: true :: y)
      = false :: false :: false :: true :: false :: true :: false :: rewriteWord y
    rw [rewriteWord, rewriteWord]

lemma X_eq (n : ℕ) : X n = G 0 n ++ WP n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e2 : hmap (WP n 0) = WP (n + 1) 0 := by
      have e := hC n 0 (by omega) [] (Or.inl rfl)
      rw [List.append_nil] at e
      rw [e]
      exact List.append_nil _
    show true :: false :: hmap (X n) = (WP 0 1 ++ G (0 + 1) n) ++ WP (n + 1) 0
    rw [ih, h_G n 0 (WP n 0) (Or.inr (headW n 0 (by omega))), e2]
    rfl

def Lw : ℕ → ℕ → ℤ
  | 0, k => (k : ℤ) + 1
  | n + 1, 0 => Lw n 1
  | n + 1, 1 => Lw n 2
  | n + 1, 2 => Lw n 4 + Lw n 0
  | n + 1, 3 => Lw n 4 + Lw n 1
  | n + 1, _ + 4 => Lw n 4 + (Lw n 3 + Lw n 0)

lemma Lw0 (n : ℕ) : Lw (n + 1) 0 = Lw n 1 := rfl
lemma Lw1 (n : ℕ) : Lw (n + 1) 1 = Lw n 2 := rfl
lemma Lw2 (n : ℕ) : Lw (n + 1) 2 = Lw n 4 + Lw n 0 := rfl
lemma Lw3 (n : ℕ) : Lw (n + 1) 3 = Lw n 4 + Lw n 1 := rfl
lemma Lw4 (n : ℕ) : Lw (n + 1) 4 = Lw n 4 + (Lw n 3 + Lw n 0) := rfl

lemma len_WP (n : ℕ) : ∀ k : ℕ, k ≤ 4 → ((WP n k).length : ℤ) = Lw n k := by
  induction n with
  | zero =>
    intro k _
    show (((true :: List.replicate k false).length : ℕ) : ℤ) = (k : ℤ) + 1
    rw [List.length_cons, List.length_replicate]
    exact Nat.cast_succ k
  | succ n ih =>
    intro k hk
    interval_cases k
    · rw [WP0, Lw0]
      exact ih 1 (by omega)
    · rw [WP1, Lw1]
      exact ih 2 (by omega)
    · rw [WP2, Lw2, List.length_append]
      push_cast
      rw [ih 4 (by omega), ih 0 (by omega)]
    · rw [WP3, Lw3, List.length_append]
      push_cast
      rw [ih 4 (by omega), ih 1 (by omega)]
    · rw [WP4, Lw4, List.length_append, List.length_append]
      push_cast
      rw [ih 4 (by omega), ih 3 (by omega), ih 0 (by omega)]

def Sg : ℕ → ℕ → ℤ
  | _, 0 => 0
  | m, n + 1 => Lw m 1 + Sg (m + 1) n

lemma lenG (n : ℕ) : ∀ m : ℕ, ((G m n).length : ℤ) = Sg m n := by
  induction n with
  | zero =>
    intro m
    rfl
  | succ n ih =>
    intro m
    show (((WP m 1 ++ G (m + 1) n).length : ℕ) : ℤ) = Lw m 1 + Sg (m + 1) n
    rw [List.length_append]
    push_cast
    rw [len_WP m 1 (by omega), ih (m + 1)]

lemma Sg_end (n : ℕ) : ∀ m : ℕ, Sg m (n + 1) = Sg m n + Lw (m + n) 1 := by
  induction n with
  | zero =>
    intro m
    show Lw m 1 + 0 = 0 + Lw (m + 0) 1
    rw [Nat.add_zero]
    ring
  | succ n ih =>
    intro m
    have e1 : Sg m (n + 1 + 1) = Lw m 1 + Sg (m + 1) (n + 1) := rfl
    have e2 : Sg m (n + 1) = Lw m 1 + Sg (m + 1) n := rfl
    rw [e1, ih (m + 1), e2, show m + 1 + n = m + (n + 1) by omega]
    ring

lemma s_succ (n : ℕ) : Sg 0 (n + 1) = Sg 0 n + Lw n 1 := by
  have e := Sg_end n 0
  rw [Nat.zero_add] at e
  exact e

lemma inv (n : ℕ) : Lw n 1 + Lw n 4 = Lw n 2 + Lw n 3 := by
  induction n with
  | zero =>
    show ((1 : ℕ) : ℤ) + 1 + (((4 : ℕ) : ℤ) + 1) = ((2 : ℕ) : ℤ) + 1 + (((3 : ℕ) : ℤ) + 1)
    norm_num
  | succ n ih =>
    rw [Lw1, Lw4, Lw2, Lw3]
    linarith

def T (n : ℕ) : ℤ := 3 + Sg 0 n + Lw n 0

lemma Trec (n : ℕ) : T (n + 5) = 3 * T (n + 4) - 3 * T (n + 3) + 3 * T (n + 2) - 3 * T (n + 1) + T n := by
  unfold T
  have i := inv n
  simp only [s_succ, Lw0, Lw1, Lw2, Lw3, Lw4]
  linarith

open OMA.S_oeis_a288380 in
lemma a_rec (m : ℕ) : a (m + 5) = 3 * a (m + 4) - 3 * a (m + 3) + 3 * a (m + 2) - 3 * a (m + 1) + a m := by
  rw [a]

open OMA.S_oeis_a288380 in
lemma a_eq (n : ℕ) : a (n + 1) = T n ∧ a (n + 2) = T (n + 1) ∧ a (n + 3) = T (n + 2) ∧
    a (n + 4) = T (n + 3) ∧ a (n + 5) = T (n + 4) := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    refine ⟨h2, h3, h4, h5, ?_⟩
    have ra := a_rec (n + 1)
    have rt := Trec n
    show a (n + 1 + 5) = T (n + 5)
    rw [ra]
    show 3 * a (n + 5) - 3 * a (n + 4) + 3 * a (n + 3) - 3 * a (n + 2) + a (n + 1) = T (n + 5)
    rw [h5, h4, h3, h2, h1, rt]

end A288380Aux

open OMA.S_oeis_a288380 A288380Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a288380.main := by
  intro n
  rcases n with _ | n
  · rfl
  · rw [word_succ, X_eq, (a_eq n).1]
    unfold T
    simp only [List.length_cons, List.length_append]
    push_cast
    rw [lenG, len_WP n 0 (by omega)]
    ring
