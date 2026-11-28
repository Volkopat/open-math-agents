import OMAStatements.S_oeis_a026488
import Mathlib

/-!
OEIS A026488: a(2) = 3 and a(n) = 3n - 5 for n ≥ 3.

Strong induction. Suppose a(1) = 1, a(2) = 3 and a(k) = 3k - 5 for 3 ≤ k ≤ m, with m ≥ 3.
All terms except a(2) = 3 are congruent to 1 modulo 3, and so is the candidate x = 3m - 2.
* x = 3m - 2 is admissible: a product of two terms is 0 or 1 modulo 3, so v(i) v(j) - v(k) = x
  forces v(k) = 3, hence k = 2 and i, j ≤ 2, where the values 1 - 3, 3 - 3, 9 - 3 are too small
  or divisible by 3.
* x = 3m - 4 is not admissible: 3 * 3 - 4 = 5 for m = 3, and for m ≥ 4, with p = (m + 3) / 2 and
  q = 3p - m - 2, we have 3 ≤ p ≤ q ≤ m and 3 a(p) - a(q) = 3m - 4.
* x = 3m - 3 is not admissible: 3 * 3 - 3 = 6 for m = 3, and for m ≥ 4, with p = (m + 6) / 3 and
  q = 4p - m - 4, we have 3 ≤ p ≤ q ≤ m and 4 a(p) - a(q) = 3m - 3.
So a(m + 1) = 3m - 2. The first three terms are checked directly.
-/

namespace OMA.A026488

def Good (a : ℕ → ℕ) (n x : ℕ) : Prop :=
  a n < x ∧ ∀ i j k : ℕ, 1 ≤ i → i ≤ j → j ≤ k → k ≤ n + 1 →
    (((if i = n + 1 then x else a i : ℕ) : ℤ) * ((if j = n + 1 then x else a j : ℕ) : ℤ)) -
      ((if k = n + 1 then x else a k : ℕ) : ℤ) ≠ (x : ℤ)

lemma val_of_least {a : ℕ → ℕ} {n c : ℕ} (hrec : a (n + 1) = sInf {x : ℕ | Good a n x})
    (hc : Good a n c) (hmin : ∀ y, y < c → ¬ Good a n y) : a (n + 1) = c := by
  rw [hrec]
  apply IsLeast.csInf_eq
  exact ⟨hc, fun y hy => not_lt.mp (fun h => hmin y h hy)⟩

lemma two (a : ℕ → ℕ) (h1 : a 1 = 1) (hrec : a 2 = sInf {x : ℕ | Good a 1 x}) : a 2 = 3 := by
  apply val_of_least hrec
  · refine ⟨by omega, ?_⟩
    intro i j k hi hij hjk hk
    have hi' : i = 1 ∨ i = 2 := by omega
    have hj' : j = 1 ∨ j = 2 := by omega
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> rcases hk' with rfl | rfl <;>
      first
        | omega
        | norm_num [h1]
  · intro y hy hgood
    have hy2 : y = 2 := by
      have := hgood.1
      omega
    subst hy2
    have h := hgood.2 2 2 2 (by norm_num) le_rfl le_rfl le_rfl
    norm_num at h

lemma three (a : ℕ → ℕ) (h1 : a 1 = 1) (h2 : a 2 = 3)
    (hrec : a 3 = sInf {x : ℕ | Good a 2 x}) : a 3 = 4 := by
  apply val_of_least hrec
  · refine ⟨by omega, ?_⟩
    intro i j k hi hij hjk hk
    have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have hj' : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    have hk' : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;>
      rcases hk' with rfl | rfl | rfl <;>
      first
        | omega
        | norm_num [h1, h2]
  · intro y hy hgood
    have := hgood.1
    omega

lemma mul_mod3 (x y : ℕ) (hx : x % 3 = 0 ∨ x % 3 = 1) (hy : y % 3 = 0 ∨ y % 3 = 1) :
    (x * y) % 3 = 0 ∨ (x * y) % 3 = 1 := by
  have h := Nat.mul_mod x y 3
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] at h <;> omega

lemma general (a : ℕ → ℕ) (m : ℕ) (hm : 3 ≤ m) (h1 : a 1 = 1) (h2 : a 2 = 3)
    (hk : ∀ k, 3 ≤ k → k ≤ m → a k = 3 * k - 5)
    (hrec : a (m + 1) = sInf {x : ℕ | Good a m x}) : a (m + 1) = 3 * m - 2 := by
  have ham : a m = 3 * m - 5 := hk m hm le_rfl
  apply val_of_least hrec
  · refine ⟨by omega, ?_⟩
    have hval : ∀ t, 1 ≤ t → t ≤ m + 1 →
        (t = 1 ∧ (if t = m + 1 then 3 * m - 2 else a t) = 1) ∨
        (t = 2 ∧ (if t = m + 1 then 3 * m - 2 else a t) = 3) ∨
        (3 ≤ t ∧ (if t = m + 1 then 3 * m - 2 else a t) % 3 = 1) := by
      intro t ht1 ht2
      by_cases htm : t = m + 1
      · right
        right
        rw [if_pos htm]
        omega
      · rw [if_neg htm]
        by_cases ht : t = 1
        · left
          exact ⟨ht, by rw [ht, h1]⟩
        · by_cases ht' : t = 2
          · right
            left
            exact ⟨ht', by rw [ht', h2]⟩
          · right
            right
            rw [hk t (by omega) (by omega)]
            omega
    intro i j k hi hij hjk hkm heq
    have hvi := hval i hi (by omega)
    have hvj := hval j (by omega) (by omega)
    have hvk := hval k (by omega) hkm
    generalize (if i = m + 1 then 3 * m - 2 else a i) = vi at heq hvi
    generalize (if j = m + 1 then 3 * m - 2 else a j) = vj at heq hvj
    generalize (if k = m + 1 then 3 * m - 2 else a k) = vk at heq hvk
    have hN : vi * vj = (3 * m - 2) + vk := by
      have h' : ((vi * vj : ℕ) : ℤ) = (((3 * m - 2) + vk : ℕ) : ℤ) := by
        push_cast
        linarith
      exact_mod_cast h'
    have hi01 : vi % 3 = 0 ∨ vi % 3 = 1 := by omega
    have hj01 : vj % 3 = 0 ∨ vj % 3 = 1 := by omega
    have h01 := mul_mod3 vi vj hi01 hj01
    rcases hvk with ⟨-, hv1⟩ | ⟨hk2, hk3⟩ | ⟨-, hkmod⟩
    · omega
    · have hvi' : vi = 1 ∨ vi = 3 := by omega
      have hvj' : vj = 1 ∨ vj = 3 := by omega
      rcases hvi' with rfl | rfl <;> rcases hvj' with rfl | rfl <;> omega
    · omega
  · intro y hy hgood
    obtain ⟨hlt, hall⟩ := hgood
    have hne : ∀ t, t ≤ m → (if t = m + 1 then y else a t) = a t := fun t ht =>
      if_neg (by omega)
    have hcases : y = 3 * m - 4 ∨ y = 3 * m - 3 := by omega
    rcases hcases with rfl | rfl
    · rcases Nat.lt_or_ge m 4 with hm3 | hm4
      · have hm' : m = 3 := by omega
        subst hm'
        have h := hall 2 2 3 (by norm_num) le_rfl (by norm_num) (by norm_num)
        rw [hne 2 (by norm_num), hne 3 (by norm_num), h2, hk 3 le_rfl le_rfl] at h
        norm_num at h
      · obtain ⟨p, hp⟩ : ∃ p, p = (m + 3) / 2 := ⟨_, rfl⟩
        obtain ⟨q, hq⟩ : ∃ q, q = 3 * p - m - 2 := ⟨_, rfl⟩
        have h := hall 2 p q (by norm_num) (by omega) (by omega) (by omega)
        rw [hne 2 (by omega), hne p (by omega), hne q (by omega), h2,
          hk p (by omega) (by omega), hk q (by omega) (by omega)] at h
        apply h
        omega
    · rcases Nat.lt_or_ge m 4 with hm3 | hm4
      · have hm' : m = 3 := by omega
        subst hm'
        have h := hall 2 2 2 (by norm_num) le_rfl le_rfl (by norm_num)
        rw [hne 2 (by norm_num), h2] at h
        norm_num at h
      · obtain ⟨p, hp⟩ : ∃ p, p = (m + 6) / 3 := ⟨_, rfl⟩
        obtain ⟨q, hq⟩ : ∃ q, q = 4 * p - m - 4 := ⟨_, rfl⟩
        have h := hall 3 p q (by norm_num) (by omega) (by omega) (by omega)
        rw [hne 3 (by omega), hne p (by omega), hne q (by omega), hk 3 le_rfl (by omega),
          hk p (by omega) (by omega), hk q (by omega) (by omega)] at h
        apply h
        omega

end OMA.A026488

open OMA.S_oeis_a026488 OMA.A026488 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026488.main := by
  rintro a ⟨h1, hrec⟩
  have hrec' : ∀ n, 1 ≤ n → a (n + 1) = sInf {x : ℕ | Good a n x} := fun n hn => hrec n hn
  have h2 : a 2 = 3 := two a h1 (hrec' 1 le_rfl)
  have h3 : a 3 = 4 := three a h1 h2 (hrec' 2 (by norm_num))
  have key : ∀ n, 3 ≤ n → a n = 3 * n - 5 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases Nat.lt_or_ge n 4 with h | h
      · have hn3 : n = 3 := by omega
        subst hn3
        exact h3
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have hgen := general a m (by omega) h1 h2 (fun k hk3 hkm => ih k (by omega) hk3)
          (hrec' m (by omega))
        rw [hgen]
        omega
  exact ⟨h2, key⟩
