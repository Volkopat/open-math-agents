import OMAStatements.S_oeis_a322069

namespace OMA.S_oeis_a322069

open Finset

/-!
## Proof of OEIS A322069 (Zhi-Wei Sun, 2018)

For every `n > 5`, we construct an explicit permutation `f` of `{1, ..., n}` with `f 1 < f n`
and `∑ k ∈ Icc 1 (n - 1), 1 / (f k * f (k + 1)) = 1`.

For `n ∈ {6, 7, 8, 9, 10, 11}`, we exhibit explicit permutations directly.
For `n ≥ 12`, we start from the 12-element base permutation
`[9, 2, 1, 4, 5, 12, 3, 11, 8, 7, 6, 10]`
and repeatedly apply the sum-preserving insertion identity
`1 / (a * (a + d)) + 1 / ((a + d) * d) = 1 / (a * d)`
along the four disjoint generating edges `(12, 3)`, `(3, 11)`, `(7, 6)`, and `(6, 10)`.
These four progressions (`0 mod 3`, `2 mod 3`, `1 mod 6`, `4 mod 6`) partition all integers `≥ 13`
and leave the endpoints `f 1 = 9 < 10 = f n` and the adjacent-product reciprocal sum `= 1` invariant.
-/

private def adjSum : List ℕ → ℚ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (1 : ℚ) / ((a : ℚ) * (b : ℚ)) + adjSum (b :: t)

private lemma adjSum_append_cons (l₁ : List ℕ) (x : ℕ) (l₂ : List ℕ) :
    adjSum (l₁ ++ x :: l₂) = adjSum (l₁ ++ [x]) + adjSum (x :: l₂) := by
  induction l₁ with
  | nil => simp [adjSum]
  | cons a t ih =>
    cases t with
    | nil => simp [adjSum]
    | cons b t' =>
      simp only [List.cons_append, adjSum] at ih ⊢
      rw [ih]
      ring

private lemma adjSum_reverse (l : List ℕ) : adjSum l.reverse = adjSum l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => simp [adjSum]
    | cons b t' =>
      simp only [List.reverse_cons]
      have h1 : (t'.reverse ++ [b]) ++ [a] = t'.reverse ++ b :: [a] := by simp
      rw [h1, adjSum_append_cons]
      simp only [List.reverse_cons] at ih
      rw [ih]
      simp only [adjSum, add_zero]
      ring

private def chainUp (a d k : ℕ) : List ℕ :=
  (List.range (k + 1)).map (fun i => a + i * d)

private lemma chainUp_zero (a d : ℕ) : chainUp a d 0 = [a] := by
  simp [chainUp]

private lemma chainUp_succ (a d k : ℕ) :
    chainUp a d (k + 1) = a :: chainUp (a + d) d k := by
  conv_lhs =>
    rw [chainUp, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, zero_mul, add_zero]
  rw [chainUp]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  ring

private lemma chainUp_length (a d k : ℕ) : (chainUp a d k).length = k + 1 := by
  simp [chainUp]

private lemma chainUp_head (a d k : ℕ) :
    ∃ t, chainUp a d k = a :: t := by
  cases k with
  | zero => exact ⟨[], chainUp_zero a d⟩
  | succ k => exact ⟨chainUp (a + d) d k, chainUp_succ a d k⟩

private lemma chainUp_last (a d k : ℕ) :
    ∃ init, chainUp a d k = init ++ [a + k * d] := by
  refine ⟨(List.range k).map (fun i => a + i * d), ?_⟩
  simp [chainUp, List.range_succ]

private lemma mem_chainUp_iff (a d k x : ℕ) :
    x ∈ chainUp a d k ↔ ∃ i ≤ k, x = a + i * d := by
  simp only [chainUp, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, Nat.lt_succ_iff.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, Nat.lt_succ_of_le hi, rfl⟩

private lemma adjSum_chainUp_append (a d k : ℕ) (ha : 0 < a) (hd : 0 < d) :
    adjSum (chainUp a d k ++ [d]) = (1 : ℚ) / ((a : ℚ) * (d : ℚ)) := by
  induction k generalizing a with
  | zero =>
    simp [chainUp_zero, adjSum]
  | succ k ih =>
    rw [chainUp_succ]
    obtain ⟨t, ht⟩ := chainUp_head (a + d) d k
    have hcons : (a :: chainUp (a + d) d k) ++ [d] = a :: (a + d) :: (t ++ [d]) := by
      simp [ht]
    rw [hcons, adjSum]
    have hback : (a + d) :: (t ++ [d]) = chainUp (a + d) d k ++ [d] := by
      simp [ht]
    rw [hback, ih (a + d) (by omega)]
    have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have had' : ((a + d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast at had' ⊢
    field_simp [ha', hd', had']
    ring

private lemma adjSum_cons_chainUp_reverse (a d k : ℕ) (ha : 0 < a) (hd : 0 < d) :
    adjSum (d :: (chainUp a d k).reverse) = (1 : ℚ) / ((d : ℚ) * (a : ℚ)) := by
  have hrev : (d :: (chainUp a d k).reverse).reverse = chainUp a d k ++ [d] := by
    simp
  rw [← adjSum_reverse, hrev, adjSum_chainUp_append a d k ha hd]
  ring

private lemma adjSum_eq_finset_sum (l : List ℕ) :
    adjSum l =
      ∑ k ∈ Icc 1 (l.length - 1),
        (1 : ℚ) / ((l.getD (k - 1) 0 : ℚ) * (l.getD k 0 : ℚ)) := by
  induction l with
  | nil => simp [adjSum]
  | cons a t ih =>
    cases t with
    | nil => simp [adjSum]
    | cons b t' =>
      simp only [adjSum, List.length_cons, Nat.add_sub_cancel] at ih ⊢
      have hsplit : Icc 1 (t'.length + 1) = insert 1 (Icc 2 (t'.length + 1)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      simp only [Nat.sub_self, List.getD_cons_zero, List.getD_cons_succ]
      congr 1
      rw [ih]
      refine Finset.sum_nbij (fun k => k + 1) ?_ ?_ ?_ ?_
      · intro k hk; simp only [mem_Icc] at hk ⊢; omega
      · intro k₁ _ k₂ _ heq; dsimp only at heq; omega
      · intro k hk
        simp only [Finset.mem_coe, mem_Icc] at hk
        exact ⟨k - 1, Finset.mem_coe.mpr (mem_Icc.mpr ⟨by omega, by omega⟩), by dsimp only; omega⟩
      · intro k hk
        simp only [mem_Icc] at hk
        have hk1 : k + 1 - 1 = k := by omega
        rw [hk1]
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨j, rfl⟩
        simp

private lemma exists_from_list (n : ℕ) (l : List ℕ) (hlen : l.length = n)
    (hmem_sub : ∀ x ∈ l, 1 ≤ x ∧ x ≤ n)
    (hsurj : ∀ x, 1 ≤ x → x ≤ n → x ∈ l)
    (hend : l.getD 0 0 < l.getD (n - 1) 0)
    (hsum : adjSum l = 1) :
    ∃ f : ℕ → ℕ, Set.BijOn f (Set.Icc 1 n) (Set.Icc 1 n) ∧ f 1 < f n ∧
      ∑ k ∈ Icc 1 (n - 1), (1 : ℚ) / ((f k : ℚ) * (f (k + 1) : ℚ)) = 1 := by
  let f : ℕ → ℕ := fun k => l.getD (k - 1) 0
  have hmaps : Set.MapsTo f (Set.Icc 1 n) (Set.Icc 1 n) := by
    intro k hk
    simp only [Set.mem_Icc] at hk ⊢
    have hlt : k - 1 < l.length := by omega
    have hval : f k = l[k - 1] := by simp [f, List.getD_eq_getElem?_getD, hlt]
    rw [hval]
    exact hmem_sub _ (List.getElem_mem hlt)
  have hsurj_on : Set.SurjOn f (Set.Icc 1 n) (Set.Icc 1 n) := by
    intro x hx
    simp only [Set.mem_Icc] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (hsurj x hx.1 hx.2)
    refine ⟨i + 1, Set.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simp [f, List.getD_eq_getElem?_getD, hi]
  have hinj_on : Set.InjOn f (Set.Icc 1 n) := by
    have himg : (Icc 1 n).image f = Icc 1 n := by
      ext x
      simp only [Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact hmaps hk
      · intro hx
        obtain ⟨k, hk, rfl⟩ := hsurj_on hx
        exact ⟨k, hk, rfl⟩
    have hcard_eq : ((Icc 1 n).image f).card = (Icc 1 n).card := congr_arg Finset.card himg
    simpa only [coe_Icc] using Finset.card_image_iff.mp hcard_eq
  refine ⟨f, ⟨hmaps, hinj_on, hsurj_on⟩, ?_, ?_⟩
  · simpa [f] using hend
  · have hsum' := adjSum_eq_finset_sum l
    rw [hlen, hsum] at hsum'
    simpa [f] using hsum'.symm

private def listLarge (n : ℕ) : List ℕ :=
  [9, 2, 1, 4, 5] ++
    chainUp 12 3 ((n - 12) / 3) ++
    [3] ++
    (chainUp 11 3 ((n - 11) / 3)).reverse ++
    [8] ++
    chainUp 7 6 ((n - 7) / 6) ++
    [6] ++
    (chainUp 10 6 ((n - 10) / 6)).reverse

private lemma listLarge_length (n : ℕ) (hn : 12 ≤ n) : (listLarge n).length = n := by
  simp only [listLarge, List.length_append, List.length_cons, List.length_nil,
    List.length_reverse, chainUp_length]
  omega

private lemma listLarge_mem_sub (n : ℕ) (hn : 12 ≤ n) :
    ∀ x ∈ listLarge n, 1 ≤ x ∧ x ≤ n := by
  intro x hx
  simp only [listLarge, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_reverse, mem_chainUp_iff] at hx
  rcases hx with (((((((h | ⟨i, hi, rfl⟩) | rfl) | ⟨i, hi, rfl⟩) | rfl) | ⟨i, hi, rfl⟩) | rfl) | ⟨i, hi, rfl⟩)
  · rcases h with rfl | rfl | rfl | rfl | rfl <;> omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private lemma listLarge_surj (n : ℕ) (hn : 12 ≤ n) :
    ∀ x, 1 ≤ x → x ≤ n → x ∈ listLarge n := by
  intro x hx1 hxn
  simp only [listLarge, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_reverse, mem_chainUp_iff]
  by_cases h12 : x < 12
  · have : x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨
        x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 10 ∨ x = 11 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; left; left; left; left; left; left; right; right; left; rfl
    · left; left; left; left; left; left; left; right; left; rfl
    · left; left; left; left; left; right; rfl
    · left; left; left; left; left; left; left; right; right; right; left; rfl
    · left; left; left; left; left; left; left; right; right; right; right; rfl
    · left; right; rfl
    · left; left; right; exact ⟨0, by omega, by omega⟩
    · left; left; left; right; rfl
    · left; left; left; left; left; left; left; left; rfl
    · right; exact ⟨0, by omega, by omega⟩
    · left; left; left; left; right; exact ⟨0, by omega, by omega⟩
  · have hmod : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by omega
    rcases hmod with h0 | h1 | h2 | h3 | h4 | h5
    · left; left; left; left; left; left; right; exact ⟨(x - 12) / 3, by omega, by omega⟩
    · left; left; right; exact ⟨(x - 7) / 6, by omega, by omega⟩
    · left; left; left; left; right; exact ⟨(x - 11) / 3, by omega, by omega⟩
    · left; left; left; left; left; left; right; exact ⟨(x - 12) / 3, by omega, by omega⟩
    · right; exact ⟨(x - 10) / 6, by omega, by omega⟩
    · left; left; left; left; right; exact ⟨(x - 11) / 3, by omega, by omega⟩

private lemma listLarge_ends (n : ℕ) (hn : 12 ≤ n) :
    (listLarge n).getD 0 0 < (listLarge n).getD (n - 1) 0 := by
  have h0 : (listLarge n).getD 0 0 = 9 := by
    simp [listLarge]
  obtain ⟨t4, ht4⟩ := chainUp_head 10 6 ((n - 10) / 6)
  have hlast_eq : ∃ pref, listLarge n = pref ++ [10] := by
    refine ⟨[9, 2, 1, 4, 5] ++ chainUp 12 3 ((n - 12) / 3) ++ [3] ++
      (chainUp 11 3 ((n - 11) / 3)).reverse ++ [8] ++ chainUp 7 6 ((n - 7) / 6) ++
      [6] ++ t4.reverse, ?_⟩
    simp [listLarge, ht4, List.append_assoc]
  obtain ⟨pref, hpref⟩ := hlast_eq
  have hlen : pref.length = n - 1 := by
    have := listLarge_length n hn
    rw [hpref, List.length_append, List.length_singleton] at this
    omega
  have hlast : (listLarge n).getD (n - 1) 0 = 10 := by
    rw [hpref, ← hlen, List.getD_eq_getElem?_getD]
    simp
  rw [h0, hlast]
  omega

private lemma listLarge_adjSum (n : ℕ) : adjSum (listLarge n) = 1 := by
  set k₁ := (n - 12) / 3
  set k₂ := (n - 11) / 3
  set k₃ := (n - 7) / 6
  set k₄ := (n - 10) / 6
  obtain ⟨t₁, ht₁⟩ := chainUp_head 12 3 k₁
  obtain ⟨t₂, ht₂⟩ := chainUp_head 11 3 k₂
  obtain ⟨t₃, ht₃⟩ := chainUp_head 7 6 k₃
  obtain ⟨t₄, ht₄⟩ := chainUp_head 10 6 k₄
  -- Split listLarge n at 12, 3, 11, 7, 6 using adjSum_append_cons
  have hdecomp : listLarge n =
      [9, 2, 1, 4, 5] ++ (12 :: (t₁ ++ (3 :: (t₂.reverse ++ (11 :: (8 :: (7 :: (t₃ ++ (6 :: (t₄.reverse ++ [10])))))))))) := by
    dsimp only [listLarge]
    rw [show (n - 12) / 3 = k₁ from rfl, show (n - 11) / 3 = k₂ from rfl,
      show (n - 7) / 6 = k₃ from rfl, show (n - 10) / 6 = k₄ from rfl, ht₁, ht₂, ht₃, ht₄]
    simp [List.append_assoc]
  rw [hdecomp]
  rw [adjSum_append_cons]
  have hA : adjSum ([9, 2, 1, 4, 5] ++ [12]) = 157 / 180 := by
    norm_num [adjSum]
  rw [hA]
  have hstep1 : 12 :: (t₁ ++ (3 :: (t₂.reverse ++ (11 :: (8 :: (7 :: (t₃ ++ (6 :: (t₄.reverse ++ [10]))))))))) =
      chainUp 12 3 k₁ ++ 3 :: (t₂.reverse ++ (11 :: (8 :: (7 :: (t₃ ++ (6 :: (t₄.reverse ++ [10]))))))) := by
    simp [ht₁]
  rw [hstep1, adjSum_append_cons, adjSum_chainUp_append 12 3 k₁ (by omega) (by omega)]
  have hstep2 : 3 :: (t₂.reverse ++ (11 :: (8 :: (7 :: (t₃ ++ (6 :: (t₄.reverse ++ [10]))))))) =
      (3 :: t₂.reverse) ++ 11 :: (8 :: (7 :: (t₃ ++ (6 :: (t₄.reverse ++ [10]))))) := by
    simp
  rw [hstep2, adjSum_append_cons]
  have hrev2 : (3 :: t₂.reverse) ++ [11] = 3 :: (chainUp 11 3 k₂).reverse := by
    simp [ht₂]
  rw [hrev2, adjSum_cons_chainUp_reverse 11 3 k₂ (by omega) (by omega)]
  have hstep3 : 11 :: 8 :: 7 :: (t₃ ++ (6 :: (t₄.reverse ++ [10]))) =
      [11, 8] ++ 7 :: (t₃ ++ (6 :: (t₄.reverse ++ [10]))) := by
    simp
  rw [hstep3, adjSum_append_cons]
  have hB' : adjSum ([11, 8] ++ [7]) = 1 / 88 + 1 / 56 := by
    norm_num [adjSum]
  rw [hB']
  have hstep4 : 7 :: (t₃ ++ (6 :: (t₄.reverse ++ [10]))) =
      chainUp 7 6 k₃ ++ 6 :: (t₄.reverse ++ [10]) := by
    simp [ht₃]
  rw [hstep4, adjSum_append_cons, adjSum_chainUp_append 7 6 k₃ (by omega) (by omega)]
  have hrev4 : 6 :: (t₄.reverse ++ [10]) = 6 :: (chainUp 10 6 k₄).reverse := by
    simp [ht₄]
  rw [hrev4, adjSum_cons_chainUp_reverse 10 6 k₄ (by omega) (by omega)]
  norm_num

private lemma check_base (n : ℕ) (l : List ℕ)
    (hlen : l.length = n)
    (hmem : l.all (fun x => decide (1 ≤ x ∧ x ≤ n)) = true)
    (hsurj : (List.range n).all (fun i => decide ((i + 1) ∈ l)) = true)
    (hend : l.getD 0 0 < l.getD (n - 1) 0)
    (hsum : adjSum l = 1) :
    ∃ f : ℕ → ℕ, Set.BijOn f (Set.Icc 1 n) (Set.Icc 1 n) ∧ f 1 < f n ∧
      ∑ k ∈ Icc 1 (n - 1), (1 : ℚ) / ((f k : ℚ) * (f (k + 1) : ℚ)) = 1 := by
  refine exists_from_list n l hlen ?_ ?_ hend hsum
  · intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hmem x hx)
  · intro x hx1 hxn
    have hmem_range : x - 1 ∈ List.range n := List.mem_range.mpr (by omega)
    have h := of_decide_eq_true (List.all_eq_true.mp hsurj (x - 1) hmem_range)
    simpa [Nat.sub_add_cancel hx1] using h

private lemma main_proof : ∀ n : ℕ, 5 < n →
    ∃ f : ℕ → ℕ, Set.BijOn f (Set.Icc 1 n) (Set.Icc 1 n) ∧ f 1 < f n ∧
      ∑ k ∈ Finset.Icc 1 (n - 1), (1 : ℚ) / ((f k : ℚ) * (f (k + 1) : ℚ)) = 1 := by
  intro n hn
  by_cases h12 : 12 ≤ n
  · exact exists_from_list n (listLarge n) (listLarge_length n h12) (listLarge_mem_sub n h12)
      (listLarge_surj n h12) (listLarge_ends n h12) (listLarge_adjSum n)
  · have hcases : n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact check_base 6 [2, 1, 3, 4, 5, 6] rfl rfl rfl (by decide) (by norm_num [adjSum])
    · exact check_base 7 [2, 1, 3, 7, 4, 5, 6] rfl rfl rfl (by decide) (by norm_num [adjSum])
    · exact check_base 8 [2, 1, 3, 8, 7, 6, 5, 4] rfl rfl rfl (by decide) (by norm_num [adjSum])
    · exact check_base 9 [3, 2, 1, 5, 4, 9, 8, 7, 6] rfl rfl rfl (by decide) (by norm_num [adjSum])
    · exact check_base 10 [2, 1, 4, 3, 5, 6, 7, 8, 9, 10] rfl rfl rfl (by decide) (by norm_num [adjSum])
    · exact check_base 11 [2, 1, 4, 3, 5, 11, 6, 7, 8, 9, 10] rfl rfl rfl (by decide) (by norm_num [adjSum])

end OMA.S_oeis_a322069

theorem OMA.solution : type_of% @OMA.S_oeis_a322069.main :=
  OMA.S_oeis_a322069.main_proof
