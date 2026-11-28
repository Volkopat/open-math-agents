import OMAReductions.R_oeis_a039508_R1
import Mathlib

/-! Descent for the 3x + 5 map outside 64 residue classes modulo 1024.

On the class `x = 2^10 a + r` the iterate after `o` odd steps and `h ≤ 10` halvings is
`3^o 2^(10-h) a + y`, where `y` is the corresponding iterate of `r`; while `h < 10` the term in
`a` is even, so the parity of the iterate is that of `y` (`step_inv`, `chk_sound`). The
Boolean `chk` runs this symbolic trajectory and stops when `3^o 2^(10-h) < 2^10` and the
constant is small enough that the iterate is below `x` for every `a ≥ 1`. `chk0` follows the
start `x = r` itself until it drops below `r` or meets the six cycle values. Both are
evaluated by the kernel on all 960 admissible residues.
-/

namespace OMA.P_oeis_a039508_R1_H1

open OMA.S_oeis_a039508

def S : Finset ℕ := {1, 5, 19, 23, 187, 347}

def Bad : Finset ℕ := {3, 7, 11, 27, 43, 59, 91, 99, 123, 131, 135, 155, 171, 187, 199, 231,
  235, 251, 259, 263, 267, 283, 299, 315, 323, 347, 355, 379, 387, 391, 427, 443, 455, 491,
  507, 515, 523, 539, 555, 571, 579, 611, 635, 643, 647, 667, 683, 699, 743, 747, 763, 771,
  775, 795, 835, 859, 891, 903, 923, 939, 955, 967, 999, 1019}

/-- Symbolic run on the class `2^10 a + r`: the iterate is `3^o 2^(10-h) a + y`. -/
def chk (r : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | fuel + 1, y, o, h =>
    if h < 10 then
      if y % 2 = 0 then
        (decide (3 ^ o * 2 ^ (10 - (h + 1)) < 2 ^ 10) &&
            decide (y / 2 + 3 ^ o * 2 ^ (10 - (h + 1)) < r + 2 ^ 10)) ||
          chk r fuel (y / 2) o (h + 1)
      else
        (decide (3 ^ (o + 1) * 2 ^ (10 - h) < 2 ^ 10) &&
            decide (3 * y + 5 + 3 ^ (o + 1) * 2 ^ (10 - h) < r + 2 ^ 10)) ||
          chk r fuel (3 * y + 5) (o + 1) h
    else false

/-- Concrete run on `x = r` itself. -/
def chk0 (r : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, y => decide (y < r) || decide (y ∈ S) || chk0 r fuel (T y)

lemma step_inv (o h y a : ℕ) (hh : h < 10) :
    T (3 ^ o * 2 ^ (10 - h) * a + y) =
      if y % 2 = 0 then 3 ^ o * 2 ^ (10 - (h + 1)) * a + y / 2
      else 3 ^ (o + 1) * 2 ^ (10 - h) * a + (3 * y + 5) := by
  obtain ⟨e, he⟩ : ∃ e, 10 - h = e + 1 := ⟨9 - h, by omega⟩
  have he' : 10 - (h + 1) = e := by omega
  rw [he, he']
  have hP : 3 ^ o * 2 ^ (e + 1) * a + y = 2 * (3 ^ o * 2 ^ e * a) + y := by ring
  unfold T
  rw [hP]
  generalize hPd : 3 ^ o * 2 ^ e * a = P
  split_ifs with h1 h2 h2
  · omega
  · omega
  · omega
  · rw [← hPd, pow_succ]; ring

lemma chk_sound (r : ℕ) : ∀ fuel y o h n, chk r fuel y o h = true →
    (∀ a, T^[n] (2 ^ 10 * a + r) = 3 ^ o * 2 ^ (10 - h) * a + y) →
    ∀ a, 1 ≤ a → ∃ i, T^[i] (2 ^ 10 * a + r) < 2 ^ 10 * a + r := by
  intro fuel
  induction fuel with
  | zero => intro y o h n hc; simp [chk] at hc
  | succ fuel ih =>
    intro y o h n hc hinv a ha
    unfold chk at hc
    split_ifs at hc with hh hy
    · have hinv' : ∀ a, T^[n + 1] (2 ^ 10 * a + r) = 3 ^ o * 2 ^ (10 - (h + 1)) * a + y / 2 := by
        intro a
        rw [Function.iterate_succ_apply', hinv a, step_inv o h y a hh, if_pos hy]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases hc with ⟨c1, c2⟩ | hc
      · refine ⟨n + 1, ?_⟩
        rw [hinv' a]
        generalize 3 ^ o * 2 ^ (10 - (h + 1)) = A at c1 c2 ⊢
        nlinarith
      · exact ih _ _ _ _ hc hinv' a ha
    · have hinv' : ∀ a, T^[n + 1] (2 ^ 10 * a + r) = 3 ^ (o + 1) * 2 ^ (10 - h) * a + (3 * y + 5) := by
        intro a
        rw [Function.iterate_succ_apply', hinv a, step_inv o h y a hh, if_neg hy]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases hc with ⟨c1, c2⟩ | hc
      · refine ⟨n + 1, ?_⟩
        rw [hinv' a]
        generalize 3 ^ (o + 1) * 2 ^ (10 - h) = A at c1 c2 ⊢
        nlinarith
      · exact ih _ _ _ _ hc hinv' a ha

lemma chk0_sound (r : ℕ) : ∀ fuel y n, chk0 r fuel y = true → T^[n] r = y →
    ∃ i, T^[i] r < r ∨ T^[i] r ∈ S := by
  intro fuel
  induction fuel with
  | zero => intro y n hc; simp [chk0] at hc
  | succ fuel ih =>
    intro y n hc hn
    simp only [chk0, Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with (hc | hc) | hc
    · exact ⟨n, Or.inl (hn ▸ hc)⟩
    · exact ⟨n, Or.inr (hn ▸ hc)⟩
    · exact ih _ (n + 1) hc (by rw [Function.iterate_succ_apply', hn])

lemma table1 : ∀ r < 512, r ∉ Bad → chk r 30 r 0 0 = true := by decide +kernel
lemma table2 : ∀ r < 512, r + 512 ∉ Bad → chk (r + 512) 30 (r + 512) 0 0 = true := by
  decide +kernel
lemma table3 : ∀ r < 512, r ∉ Bad → r = 0 ∨ chk0 r 60 r = true := by decide +kernel
lemma table4 : ∀ r < 512, r + 512 ∉ Bad → chk0 (r + 512) 60 (r + 512) = true := by
  decide +kernel

theorem slice : ∀ x : ℕ, 1 ≤ x → x % 1024 ∉ Bad →
    ∃ i : ℕ, T^[i] x < x ∨ T^[i] x ∈ S := by
  intro x hx hb
  have hr : x % 1024 < 1024 := Nat.mod_lt _ (by norm_num)
  have hx' : x = 2 ^ 10 * (x / 1024) + x % 1024 := by
    have := Nat.div_add_mod x 1024; norm_num; omega
  have hc : chk (x % 1024) 30 (x % 1024) 0 0 = true := by
    by_cases h5 : x % 1024 < 512
    · exact table1 _ h5 hb
    · have := table2 (x % 1024 - 512) (by omega) (by rw [Nat.sub_add_cancel (by omega)]; exact hb)
      rwa [Nat.sub_add_cancel (by omega)] at this
  rcases Nat.eq_zero_or_pos (x / 1024) with ha | ha
  · have hxr : x = x % 1024 := by omega
    have h0 : chk0 (x % 1024) 60 (x % 1024) = true := by
      by_cases h5 : x % 1024 < 512
      · rcases table3 _ h5 hb with h | h
        · omega
        · exact h
      · have := table4 (x % 1024 - 512) (by omega)
          (by rw [Nat.sub_add_cancel (by omega)]; exact hb)
        rwa [Nat.sub_add_cancel (by omega)] at this
    rw [hxr]
    exact chk0_sound _ 60 _ 0 h0 rfl
  · rw [hx']
    obtain ⟨i, hi⟩ := chk_sound _ 30 _ 0 0 0 hc (fun a => by simp) _ ha
    exact ⟨i, Or.inl hi⟩
end OMA.P_oeis_a039508_R1_H1

theorem OMA.solution : OMA.R_oeis_a039508_R1.H1 :=
  fun x hx hb => OMA.P_oeis_a039508_R1_H1.slice x hx hb
