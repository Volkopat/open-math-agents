import OMAStatements.S_oeis_a088023

namespace OMA.A088023Proof

open OMA.S_oeis_a088023

private lemma step_length (L : List ℕ) : (step L).length = 2 * L.length := by
  simp [step]
  omega

private lemma block_length (k : ℕ) : (block k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [block, step_length, ih, Nat.pow_succ]
    omega

private lemma step_getElem_left (L : List ℕ) (i : ℕ) (hi : i < L.length) :
    (step L)[i]'(by rw [step_length]; omega) = L[i] := by
  simp [step, List.getElem_append_left hi]

private lemma step_getElem_right (L : List ℕ) (j : ℕ) (hj : j < L.length) :
    (step L)[L.length + j]'(by rw [step_length]; omega) =
      L[L.length - 1 - j]'(by omega) + (j + 1) := by
  simp only [step]
  rw [List.getElem_append_right (by omega)]
  have hsub : L.length + j - L.length = j := by omega
  simp only [hsub, List.getElem_map, List.getElem_zipIdx, List.getElem_reverse]
  omega

private lemma block_getElem_le {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (i : ℕ) (hi : i < (block k₁).length) :
    (block k₂)[i]'(by
      rw [block_length] at hi ⊢
      exact Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) hk)) =
      (block k₁)[i] := by
  induction hk with
  | refl => rfl
  | @step m hm ih =>
    rw [← ih]
    exact step_getElem_left (block m) i (by
      rw [block_length] at hi ⊢
      exact Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) hm))

private lemma step_bound (L : List ℕ) (hL : 0 < L.length)
    (ih : ∀ i (hi : i + 1 < L.length), L[i] ≤ L[i + 1] ∧ L[i + 1] ≤ L[i] + 1) :
    ∀ i (hi : i + 1 < (step L).length),
      (step L)[i] ≤ (step L)[i + 1] ∧ (step L)[i + 1] ≤ (step L)[i] + 1 := by
  intro i hi
  rw [step_length] at hi
  by_cases h1 : i + 1 < L.length
  · rw [step_getElem_left L i (by omega), step_getElem_left L (i + 1) h1]
    exact ih i h1
  · by_cases h2 : i + 1 = L.length
    · have hiL : i = L.length - 1 := by omega
      have hleft : (step L)[i]'(by rw [step_length]; omega) = L[L.length - 1]'(by omega) := by
        rw [step_getElem_left L i (by omega)]
        congr 1
      have hright : (step L)[i + 1]'(by rw [step_length]; omega) =
          L[L.length - 1]'(by omega) + 1 := by
        have h := step_getElem_right L 0 hL
        have heq : i + 1 = L.length + 0 := by omega
        simp only [heq]
        simpa using h
      rw [hleft, hright]
      omega
    · have hge : L.length ≤ i := by omega
      let j := i - L.length
      have hj1 : j + 1 < L.length := by omega
      have hi1 : i = L.length + j := by omega
      have hi2 : i + 1 = L.length + (j + 1) := by omega
      have hleft : (step L)[i]'(by rw [step_length]; omega) =
          L[L.length - 1 - j]'(by omega) + (j + 1) := by
        simp only [hi1]
        exact step_getElem_right L j (by omega)
      have hright : (step L)[i + 1]'(by rw [step_length]; omega) =
          L[L.length - 1 - (j + 1)]'(by omega) + (j + 2) := by
        simp only [hi2]
        exact step_getElem_right L (j + 1) hj1
      rw [hleft, hright]
      have hm := ih (L.length - 1 - (j + 1)) (by omega)
      have hidx : L.length - 1 - (j + 1) + 1 = L.length - 1 - j := by omega
      simp only [hidx] at hm
      omega

private lemma block_bound (k : ℕ) :
    ∀ i (hi : i + 1 < (block k).length),
      (block k)[i] ≤ (block k)[i + 1] ∧ (block k)[i + 1] ≤ (block k)[i] + 1 := by
  induction k with
  | zero =>
    intro i hi
    simp [block] at hi
  | succ k ih =>
    apply step_bound (block k)
    · rw [block_length]; exact Nat.two_pow_pos k
    · exact ih

end OMA.A088023Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a088023.main := by
  intro n hn
  have h1 : n - 1 < (OMA.S_oeis_a088023.block (Nat.log2 n + 1)).length := by
    rw [OMA.A088023Proof.block_length]
    have := Nat.lt_log2_self (n := n)
    omega
  have h2 : n < (OMA.S_oeis_a088023.block (Nat.log2 (n + 1) + 1)).length := by
    rw [OMA.A088023Proof.block_length]
    have := Nat.lt_log2_self (n := n + 1)
    omega
  have ha1 : OMA.S_oeis_a088023.a n = (OMA.S_oeis_a088023.block (Nat.log2 n + 1))[n - 1]'h1 := by
    simp only [OMA.S_oeis_a088023.a, hn, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, Option.getD_some]
  have ha2 : OMA.S_oeis_a088023.a (n + 1) =
      (OMA.S_oeis_a088023.block (Nat.log2 (n + 1) + 1))[n]'h2 := by
    have hn1 : 1 ≤ n + 1 := by omega
    simp only [OMA.S_oeis_a088023.a, hn1, ↓reduceIte, Nat.add_sub_cancel,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  let k := max (Nat.log2 n + 1) (Nat.log2 (n + 1) + 1)
  have hk1 : Nat.log2 n + 1 ≤ k := Nat.le_max_left _ _
  have hk2 : Nat.log2 (n + 1) + 1 ≤ k := Nat.le_max_right _ _
  rw [ha1, ha2, ← OMA.A088023Proof.block_getElem_le hk1 (n - 1) h1,
    ← OMA.A088023Proof.block_getElem_le hk2 n h2]
  have hlen : (n - 1) + 1 < (OMA.S_oeis_a088023.block k).length := by
    rw [OMA.A088023Proof.block_length] at h2 ⊢
    have := Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) hk2)
    omega
  have hb := (OMA.A088023Proof.block_bound k (n - 1) hlen).1
  have hidx : n - 1 + 1 = n := by omega
  simpa [hidx] using hb
