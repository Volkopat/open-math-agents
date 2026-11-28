import OMAStatements.S_oeis_a167493
import Mathlib

/-!
# Disproof of the first A167493 conjecture

The first conjecture (every difference a(n) - a(n-1), n >= 2, is 1 or prime) fails at
n = 620757: a(620756) = 1241460, a(620757) = 1241487, difference 27. This is the failure
recorded in OEIS A167493 by Bill McEachen (Jan 20 2023). The values are obtained by
iterating the defining step from a(1) = 2 in blocks of 20000 steps, each block checked by
kernel evaluation (decide +kernel; no native code, no extra axioms).
-/

namespace OMA.P_oeis_a167493

open OMA.S_oeis_a167493

/-- k further steps starting from the value v at index n. -/
def it : ℕ → ℕ → ℕ → ℕ
  | 0, _, v => v
  | k + 1, n, v => it k (n + 1) (step (n + 1) v)

lemma a_succ (n : ℕ) (hn : 1 ≤ n) : a (n + 1) = step (n + 1) (a n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

lemma a_it (k : ℕ) : ∀ n m : ℕ, 1 ≤ n → n + k = m → a m = it k n (a n) := by
  induction k with
  | zero => intro n m _ h; subst h; rfl
  | succ k ih =>
    intro n m hn h
    rw [ih (n + 1) m (by omega) (by omega), a_succ n hn]
    rfl

lemma c0 : it 20000 1 2 = 39141 := by decide +kernel

lemma c1 : it 20000 20001 39141 = 78569 := by decide +kernel

lemma c2 : it 20000 40001 78569 = 98569 := by decide +kernel

lemma c3 : it 20000 60001 98569 = 157419 := by decide +kernel

lemma c4 : it 20000 80001 157419 = 177419 := by decide +kernel

lemma c5 : it 20000 100001 177419 = 197419 := by decide +kernel

lemma c6 : it 20000 120001 197419 = 217419 := by decide +kernel

lemma c7 : it 20000 140001 217419 = 314873 := by decide +kernel

lemma c8 : it 20000 160001 314873 = 334873 := by decide +kernel

lemma c9 : it 20000 180001 334873 = 354873 := by decide +kernel

lemma c10 : it 20000 200001 354873 = 374873 := by decide +kernel

lemma c11 : it 20000 220001 374873 = 394873 := by decide +kernel

lemma c12 : it 20000 240001 394873 = 414873 := by decide +kernel

lemma c13 : it 20000 260001 414873 = 434873 := by decide +kernel

lemma c14 : it 20000 280001 434873 = 454873 := by decide +kernel

lemma c15 : it 20000 300001 454873 = 630231 := by decide +kernel

lemma c16 : it 20000 320001 630231 = 650231 := by decide +kernel

lemma c17 : it 20000 340001 650231 = 670231 := by decide +kernel

lemma c18 : it 20000 360001 670231 = 690231 := by decide +kernel

lemma c19 : it 20000 380001 690231 = 710231 := by decide +kernel

lemma c20 : it 20000 400001 710231 = 730231 := by decide +kernel

lemma c21 : it 20000 420001 730231 = 750231 := by decide +kernel

lemma c22 : it 20000 440001 750231 = 770231 := by decide +kernel

lemma c23 : it 20000 460001 770231 = 790231 := by decide +kernel

lemma c24 : it 20000 480001 790231 = 810231 := by decide +kernel

lemma c25 : it 20000 500001 810231 = 830231 := by decide +kernel

lemma c26 : it 20000 520001 830231 = 850231 := by decide +kernel

lemma c27 : it 20000 540001 850231 = 870231 := by decide +kernel

lemma c28 : it 20000 560001 870231 = 890231 := by decide +kernel

lemma c29 : it 20000 580001 890231 = 910231 := by decide +kernel

lemma c30 : it 20000 600001 910231 = 930231 := by decide +kernel

lemma c31 : it 755 620001 930231 = 1241460 := by decide +kernel

lemma v0 : a 1 = 2 := rfl

lemma v1 : a 20001 = 39141 := by
  rw [a_it 20000 1 20001 (by norm_num) (by norm_num), v0, c0]

lemma v2 : a 40001 = 78569 := by
  rw [a_it 20000 20001 40001 (by norm_num) (by norm_num), v1, c1]

lemma v3 : a 60001 = 98569 := by
  rw [a_it 20000 40001 60001 (by norm_num) (by norm_num), v2, c2]

lemma v4 : a 80001 = 157419 := by
  rw [a_it 20000 60001 80001 (by norm_num) (by norm_num), v3, c3]

lemma v5 : a 100001 = 177419 := by
  rw [a_it 20000 80001 100001 (by norm_num) (by norm_num), v4, c4]

lemma v6 : a 120001 = 197419 := by
  rw [a_it 20000 100001 120001 (by norm_num) (by norm_num), v5, c5]

lemma v7 : a 140001 = 217419 := by
  rw [a_it 20000 120001 140001 (by norm_num) (by norm_num), v6, c6]

lemma v8 : a 160001 = 314873 := by
  rw [a_it 20000 140001 160001 (by norm_num) (by norm_num), v7, c7]

lemma v9 : a 180001 = 334873 := by
  rw [a_it 20000 160001 180001 (by norm_num) (by norm_num), v8, c8]

lemma v10 : a 200001 = 354873 := by
  rw [a_it 20000 180001 200001 (by norm_num) (by norm_num), v9, c9]

lemma v11 : a 220001 = 374873 := by
  rw [a_it 20000 200001 220001 (by norm_num) (by norm_num), v10, c10]

lemma v12 : a 240001 = 394873 := by
  rw [a_it 20000 220001 240001 (by norm_num) (by norm_num), v11, c11]

lemma v13 : a 260001 = 414873 := by
  rw [a_it 20000 240001 260001 (by norm_num) (by norm_num), v12, c12]

lemma v14 : a 280001 = 434873 := by
  rw [a_it 20000 260001 280001 (by norm_num) (by norm_num), v13, c13]

lemma v15 : a 300001 = 454873 := by
  rw [a_it 20000 280001 300001 (by norm_num) (by norm_num), v14, c14]

lemma v16 : a 320001 = 630231 := by
  rw [a_it 20000 300001 320001 (by norm_num) (by norm_num), v15, c15]

lemma v17 : a 340001 = 650231 := by
  rw [a_it 20000 320001 340001 (by norm_num) (by norm_num), v16, c16]

lemma v18 : a 360001 = 670231 := by
  rw [a_it 20000 340001 360001 (by norm_num) (by norm_num), v17, c17]

lemma v19 : a 380001 = 690231 := by
  rw [a_it 20000 360001 380001 (by norm_num) (by norm_num), v18, c18]

lemma v20 : a 400001 = 710231 := by
  rw [a_it 20000 380001 400001 (by norm_num) (by norm_num), v19, c19]

lemma v21 : a 420001 = 730231 := by
  rw [a_it 20000 400001 420001 (by norm_num) (by norm_num), v20, c20]

lemma v22 : a 440001 = 750231 := by
  rw [a_it 20000 420001 440001 (by norm_num) (by norm_num), v21, c21]

lemma v23 : a 460001 = 770231 := by
  rw [a_it 20000 440001 460001 (by norm_num) (by norm_num), v22, c22]

lemma v24 : a 480001 = 790231 := by
  rw [a_it 20000 460001 480001 (by norm_num) (by norm_num), v23, c23]

lemma v25 : a 500001 = 810231 := by
  rw [a_it 20000 480001 500001 (by norm_num) (by norm_num), v24, c24]

lemma v26 : a 520001 = 830231 := by
  rw [a_it 20000 500001 520001 (by norm_num) (by norm_num), v25, c25]

lemma v27 : a 540001 = 850231 := by
  rw [a_it 20000 520001 540001 (by norm_num) (by norm_num), v26, c26]

lemma v28 : a 560001 = 870231 := by
  rw [a_it 20000 540001 560001 (by norm_num) (by norm_num), v27, c27]

lemma v29 : a 580001 = 890231 := by
  rw [a_it 20000 560001 580001 (by norm_num) (by norm_num), v28, c28]

lemma v30 : a 600001 = 910231 := by
  rw [a_it 20000 580001 600001 (by norm_num) (by norm_num), v29, c29]

lemma v31 : a 620001 = 930231 := by
  rw [a_it 20000 600001 620001 (by norm_num) (by norm_num), v30, c30]

lemma v32 : a 620756 = 1241460 := by
  rw [a_it 755 620001 620756 (by norm_num) (by norm_num), v31, c31]

lemma vlast : a 620757 = 1241487 := by
  rw [a_it 1 620756 620757 (by norm_num) (by norm_num), v32]
  decide +kernel

end OMA.P_oeis_a167493

open OMA.S_oeis_a167493 OMA.P_oeis_a167493 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a167493.main) := by
  intro h
  have h1 := h.1 620757 (by norm_num)
  have hd : difference 620757 = 27 := by
    unfold difference
    rw [show 620757 - 1 = 620756 from rfl, vlast, v32]
  rw [hd] at h1
  norm_num at h1
