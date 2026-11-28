import OMAStatements.S_oeis_a124758
import Mathlib

namespace A124758Proof

open OMA.S_oeis_a124758

def D (prev : ℕ) (P : List ℕ) : ℕ := (List.zipWith (fun x y => y - x) (prev :: P) P).prod

lemma D_nil (prev : ℕ) : D prev [] = 1 := by simp [D]

lemma D_cons (prev p : ℕ) (P : List ℕ) : D prev (p :: P) = (p - prev) * D p P := by
  simp [D]

lemma D_shift (P : List ℕ) : ∀ prev c : ℕ, D (prev + c) (P.map (fun x => x + c)) = D prev P := by
  induction P with
  | nil => intro prev c; simp [D_nil]
  | cons p P ih =>
    intro prev c
    rw [List.map_cons, D_cons, D_cons, ih, Nat.add_sub_add_right]

lemma a_eq_D (k : ℕ) : a k = D 0 (onePos k) := by
  simp [a, comp, D, List.prod_reverse]

def pos (d : List ℕ) : List ℕ :=
  ((List.range d.length).filter (fun i => d.getD i 0 = 1)).map (· + 1)

lemma onePos_eq (k : ℕ) : onePos k = pos (Nat.digits 2 k) := rfl

lemma pos_cons (b : ℕ) (d : List ℕ) :
    pos (b :: d) = (if b = 1 then [1] else []) ++ (pos d).map (· + 1) := by
  unfold pos
  rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
  by_cases hb : b = 1
  · subst hb
    simp [List.map_map, Function.comp_def]
  · simp [hb, List.map_map, Function.comp_def]

lemma digits_odd (n : ℕ) : Nat.digits 2 (2 * n + 1) = 1 :: Nat.digits 2 n := by
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [Nat.digits_def' (by norm_num) (by omega), h1, h2]

lemma digits_even (n : ℕ) (hn : 0 < n) : Nat.digits 2 (2 * n) = 0 :: Nat.digits 2 n := by
  have h1 : (2 * n) % 2 = 0 := by omega
  have h2 : (2 * n) / 2 = n := by omega
  rw [Nat.digits_def' (by norm_num) (by omega), h1, h2]

lemma onePos_odd (n : ℕ) : onePos (2 * n + 1) = 1 :: (onePos n).map (· + 1) := by
  rw [onePos_eq (2 * n + 1), onePos_eq n, digits_odd, pos_cons]
  simp

lemma onePos_zero : onePos 0 = [] := by simp [onePos]

lemma onePos_even (n : ℕ) : onePos (2 * n) = (onePos n).map (· + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [onePos_zero]
  · rw [onePos_eq (2 * n), onePos_eq n, digits_even n hn, pos_cons]
    simp

lemma onePos_K (f j : ℕ) :
    onePos (2 ^ f * (2 * j + 1)) = (f + 1) :: (onePos j).map (fun x => x + (f + 1)) := by
  induction f with
  | zero => simp [onePos_odd]
  | succ f ih =>
    rw [show 2 ^ (f + 1) * (2 * j + 1) = 2 * (2 ^ f * (2 * j + 1)) by ring, onePos_even, ih]
    have hfun : ((· + 1) ∘ fun x => x + (f + 1)) = fun x => x + (f + 1 + 1) := by
      funext x
      show x + (f + 1) + 1 = x + (f + 1 + 1)
      omega
    rw [List.map_cons, List.map_map, hfun]

lemma a_zero : a 0 = 1 := by
  rw [a_eq_D, onePos_zero, D_nil]

lemma K (f j : ℕ) : a (2 ^ f * (2 * j + 1)) = (f + 1) * a j := by
  rw [a_eq_D, onePos_K, D_cons, Nat.sub_zero, a_eq_D j]
  have h := D_shift (onePos j) 0 (f + 1)
  rw [Nat.zero_add] at h
  rw [h]

lemma decomp : ∀ n : ℕ, 0 < n → ∃ f j : ℕ, n = 2 ^ f * (2 * j + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
    · obtain ⟨f, j, hfj⟩ := ih m (by omega) (by omega)
      exact ⟨f + 1, j, by rw [hm, hfj]; ring⟩
    · exact ⟨0, m, by rw [hm]; ring⟩

lemma V (f j : ℕ) : padicValNat 2 (2 ^ f * (2 * j + 1)) = f := by
  rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by omega), Nat.add_zero]

theorem part1 (n : ℕ) : a (2 * n + 1) = a n := by
  have h := K 0 n
  simpa using h

theorem part2 (n : ℕ) (hn : 0 < n) :
    (a (2 * n) : ℚ) = (1 + 1 / (padicValNat 2 (2 * n) : ℚ)) * a n ∧
    (a (2 * n) : ℤ) = 2 * a n + a (n - 2 ^ padicValNat 2 n) - a (2 * n - 2 ^ padicValNat 2 n) := by
  obtain ⟨f, j, rfl⟩ := decomp n hn
  have e1 : 2 * (2 ^ f * (2 * j + 1)) = 2 ^ (f + 1) * (2 * j + 1) := by ring
  have hs1 : 2 ^ f * (2 * j + 1) - 2 ^ f = 2 ^ (f + 1) * j :=
    Nat.sub_eq_of_eq_add (by ring)
  have hs2 : 2 * (2 ^ f * (2 * j + 1)) - 2 ^ f = 2 ^ f * (2 * (2 * j) + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [V f j, hs1, hs2, e1, V (f + 1) j, K (f + 1) j, K f j, K f (2 * j)]
  constructor
  · have hf : ((f : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    try ring
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [mul_zero, a_zero]
      push_cast
      ring
    · obtain ⟨g, i, rfl⟩ := decomp j hj
      rw [show 2 ^ (f + 1) * (2 ^ g * (2 * i + 1)) = 2 ^ (f + 1 + g) * (2 * i + 1) by ring,
        show 2 * (2 ^ g * (2 * i + 1)) = 2 ^ (g + 1) * (2 * i + 1) by ring,
        K (f + 1 + g) i, K (g + 1) i, K g i]
      push_cast
      ring

theorem part3 (n : ℕ) : a (4 * n + 2) = 2 * a n ∧ (a (4 * n) : ℤ) = 2 * a (2 * n) - a n := by
  constructor
  · have h := K 1 n
    rw [show 2 ^ 1 * (2 * n + 1) = 4 * n + 2 by ring] at h
    omega
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num [a_zero]
    · obtain ⟨f, j, rfl⟩ := decomp n hn
      rw [show 4 * (2 ^ f * (2 * j + 1)) = 2 ^ (f + 2) * (2 * j + 1) by ring,
        show 2 * (2 ^ f * (2 * j + 1)) = 2 ^ (f + 1) * (2 * j + 1) by ring,
        K (f + 2) j, K (f + 1) j, K f j]
      push_cast
      ring

lemma sum_split (g : ℕ → ℤ) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), g k = ∑ k ∈ Finset.range m, (g (2 * k) + g (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    ring

theorem part4 (n : ℕ) : ((∑ k ∈ Finset.range (2 ^ n), a k : ℕ) : ℤ) = A001519 (n + 1) := by
  have key : ∀ n : ℕ, (∑ k ∈ Finset.range (2 ^ n), (a k : ℤ)) = A001519 (n + 1) ∧
      (∑ k ∈ Finset.range (2 ^ n), (a (2 * k) : ℤ)) = A001519 (n + 2) - A001519 (n + 1) := by
    intro n
    induction n with
    | zero =>
      have b1 : A001519 1 = 1 := by norm_num [A001519]
      have b2 : A001519 2 = 2 := by norm_num [A001519]
      simp [a_zero, b1, b2]
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      have hb : A001519 (n + 3) = 3 * A001519 (n + 2) - A001519 (n + 1) := rfl
      have e1 : ∑ k ∈ Finset.range (2 ^ (n + 1)), (a k : ℤ) =
          ∑ k ∈ Finset.range (2 ^ n), ((a (2 * k) : ℤ) + (a (2 * k + 1) : ℤ)) := by
        rw [show 2 ^ (n + 1) = 2 * 2 ^ n by ring]
        exact sum_split (fun k => (a k : ℤ)) (2 ^ n)
      have e2 : ∑ k ∈ Finset.range (2 ^ (n + 1)), (a (2 * k) : ℤ) =
          ∑ k ∈ Finset.range (2 ^ n), ((a (2 * (2 * k)) : ℤ) + (a (2 * (2 * k + 1)) : ℤ)) := by
        rw [show 2 ^ (n + 1) = 2 * 2 ^ n by ring]
        exact sum_split (fun k => (a (2 * k) : ℤ)) (2 ^ n)
      have e3 : ∑ k ∈ Finset.range (2 ^ n), ((a (2 * k) : ℤ) + (a (2 * k + 1) : ℤ)) =
          ∑ k ∈ Finset.range (2 ^ n), (a (2 * k) : ℤ) + ∑ k ∈ Finset.range (2 ^ n), (a k : ℤ) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [part1]
      have e4 : ∑ k ∈ Finset.range (2 ^ n), ((a (2 * (2 * k)) : ℤ) + (a (2 * (2 * k + 1)) : ℤ)) =
          2 * ∑ k ∈ Finset.range (2 ^ n), (a (2 * k) : ℤ) + ∑ k ∈ Finset.range (2 ^ n), (a k : ℤ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        have h3 := part3 k
        rw [show 2 * (2 * k) = 4 * k by ring, show 2 * (2 * k + 1) = 4 * k + 2 by ring, h3.2, h3.1]
        push_cast
        ring
      show (∑ k ∈ Finset.range (2 ^ (n + 1)), (a k : ℤ)) = A001519 (n + 2) ∧
        (∑ k ∈ Finset.range (2 ^ (n + 1)), (a (2 * k) : ℤ)) = A001519 (n + 3) - A001519 (n + 2)
      rw [e1, e2, e3, e4, h1, h2, hb]
      constructor <;> ring
  rw [Nat.cast_sum]
  exact (key n).1

def c : ℕ → ℕ
  | 0 => 0
  | n + 1 => 4 * c n + 1

lemma c_spec (n : ℕ) : 3 * c n + 1 = 4 ^ n := by
  induction n with
  | zero => simp [c]
  | succ n ih =>
    show 3 * (4 * c n + 1) + 1 = 4 ^ (n + 1)
    rw [pow_succ, ← ih]
    ring

lemma c_div (n : ℕ) : (4 ^ n - 1) / 3 = c n := by
  rw [← c_spec n]
  omega

lemma a_two_c (n : ℕ) : a (2 * c n) = 2 ^ n := by
  induction n with
  | zero => simp [c, a_zero]
  | succ n ih =>
    have e : 2 * c (n + 1) = 2 ^ 1 * (2 * (2 * c n) + 1) := by
      show 2 * (4 * c n + 1) = _
      ring
    rw [e, K 1 (2 * c n), ih]
    ring

theorem part5 (n : ℕ) : a ((4 ^ n - 1) / 3) = A011782 n := by
  rw [c_div]
  cases n with
  | zero => simp [c, a_zero, A011782]
  | succ m =>
    show a (4 * c m + 1) = A011782 (m + 1)
    rw [show 4 * c m + 1 = 2 * (2 * c m) + 1 by ring, part1, a_two_c]
    simp [A011782]

lemma a_mersenne (k : ℕ) : a (2 ^ k - 1) = 1 := by
  induction k with
  | zero => simp [a_zero]
  | succ k ih =>
    have h1 : 0 < 2 ^ k := by positivity
    have e : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by rw [pow_succ]; omega
    rw [e, part1, ih]

theorem part6 (n m : ℕ) (hn : 0 < n) : a (2 ^ m * (2 ^ n - 1)) = m + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : 0 < 2 ^ k := by positivity
  have e : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by rw [pow_succ]; omega
  rw [e, K, a_mersenne, mul_one]

end A124758Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a124758.main := by
  exact ⟨A124758Proof.part1, A124758Proof.part2, A124758Proof.part3, A124758Proof.part4,
    A124758Proof.part5, A124758Proof.part6⟩

