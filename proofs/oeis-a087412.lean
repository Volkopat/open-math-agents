import OMAStatements.S_oeis_a087412
import Mathlib

/-!
Write `S n f = f 0 + ... + f (n - 1)` and `G M m` for the number of pairs `(x, y)` in `[0, m)²`
with `x^3 + y^3 ≡ 1 (mod M)`, so that `a n = G n n`. For `m > 0` split `[0, 9 m)` as
`{i (3 m) + x : i < 3, x < 3 m}`:
* `(i (3 m) + x)^3 = x^3 + 9 m (i x^2 + 3 (i^2 m x + i^3 m^2))`, so the cube modulo `9 m` only
  depends on `x` modulo `3 m`; hence `G (9 m) (9 m) = 9 G (9 m) (3 m)` (and likewise for `3 m`).
* if `x^3 + y^3 ≡ 1 (mod 9 m)`, then `3 ∤ x` or `3 ∤ y`, and the shifted pair satisfies the
  congruence modulo `27 m` iff `q + i x^2 + j y^2 ≡ 0 (mod 3)` with `q = (x^3 + y^3) / (9 m)`;
  exactly three of the nine `(i, j)` work. Hence `G (27 m) (9 m) = 3 G (9 m) (3 m)`.
Together `a (27 m) = 3 a (9 m)`, and induction from `a 9 = 18` gives `a (3^e) = 2 * 3^e`.
-/

namespace R087412
open OMA.S_oeis_a087412

/-- `S n f = f 0 + ... + f (n - 1)`. -/
def S : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => S n f + f n

theorem S_zero (f : ℕ → ℕ) : S 0 f = 0 := rfl

theorem S_succ (n : ℕ) (f : ℕ → ℕ) : S (n + 1) f = S n f + f n := rfl

theorem S_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ x, x < n → f x = g x) : S n f = S n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [S_succ, S_succ, ih (fun x hx => h x (by omega)), h n (by omega)]

theorem S_add (n k : ℕ) (f : ℕ → ℕ) : S (n + k) f = S n f + S k (fun x => f (n + x)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, S_succ (n + k), ih, S_succ k]
    omega

theorem S_add_distrib (n : ℕ) (f g : ℕ → ℕ) :
    S n (fun x => f x + g x) = S n f + S n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [S_succ n (fun x => f x + g x), S_succ n f, S_succ n g, ih]
    omega

theorem S_mul (n c : ℕ) (f : ℕ → ℕ) : S n (fun x => c * f x) = c * S n f := by
  induction n with
  | zero => rw [S_zero, S_zero, Nat.mul_zero]
  | succ n ih => rw [S_succ n (fun x => c * f x), S_succ n f, ih, Nat.mul_add]

theorem S_const (n c : ℕ) : S n (fun _ => c) = n * c := by
  induction n with
  | zero => rw [S_zero, Nat.zero_mul]
  | succ n ih => rw [S_succ, ih, Nat.succ_mul]

theorem S_comm (n k : ℕ) (F : ℕ → ℕ → ℕ) :
    S n (fun x => S k (fun y => F x y)) = S k (fun y => S n (fun x => F x y)) := by
  induction n with
  | zero => exact ((S_const k 0).trans (Nat.mul_zero k)).symm
  | succ n ih =>
    rw [S_succ n (fun x => S k (fun y => F x y)), ih]
    rw [← S_add_distrib]
    rfl

theorem S_three (L : ℕ) (f : ℕ → ℕ) :
    S (3 * L) f = S L (fun x => S 3 (fun i => f (i * L + x))) := by
  have h3 : ∀ x, S 3 (fun i => f (i * L + x)) = f x + f (L + x) + f (L + L + x) := by
    intro x
    show 0 + f (0 * L + x) + f (1 * L + x) + f (2 * L + x) = _
    rw [Nat.zero_mul, Nat.one_mul, Nat.two_mul, Nat.zero_add, Nat.zero_add]
  rw [S_congr (fun x _ => h3 x), S_add_distrib, S_add_distrib,
    show 3 * L = L + L + L by omega, S_add (L + L) L f, S_add L L f]

theorem split2 (L n : ℕ) (hn : n = 3 * L) (F : ℕ → ℕ → ℕ) :
    S n (fun x => S n (fun y => F x y)) =
      S L (fun x => S L (fun y => S 3 (fun i => S 3 (fun j => F (i * L + x) (j * L + y))))) := by
  subst hn
  rw [S_three L (fun x => S (3 * L) (fun y => F x y))]
  refine S_congr fun x _ => ?_
  calc S 3 (fun i => S (3 * L) (fun y => F (i * L + x) y))
      = S 3 (fun i => S L (fun y => S 3 (fun j => F (i * L + x) (j * L + y)))) :=
        S_congr fun i _ => S_three L (fun y => F (i * L + x) y)
    _ = S L (fun y => S 3 (fun i => S 3 (fun j => F (i * L + x) (j * L + y)))) :=
        S_comm 3 L (fun i y => S 3 (fun j => F (i * L + x) (j * L + y)))

theorem card_range_filter (k : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.range k).filter p).card = S k (fun y => if p y then 1 else 0) := by
  induction k with
  | zero => rw [Finset.range_zero, Finset.filter_empty, Finset.card_empty, S_zero]
  | succ k ih =>
    rw [Finset.range_add_one, Finset.filter_insert, S_succ, ← ih]
    by_cases hk : p k
    · rw [if_pos hk, if_pos hk, Finset.card_insert_of_notMem]
      intro hmem
      rw [Finset.mem_filter, Finset.mem_range] at hmem
      omega
    · rw [if_neg hk, if_neg hk, Nat.add_zero]

theorem card_prod_filter (n k : ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R] :
    ((Finset.range n ×ˢ Finset.range k).filter (fun p => R p.1 p.2)).card =
      S n (fun x => S k (fun y => if R x y then 1 else 0)) := by
  induction n with
  | zero =>
    rw [S_zero, Finset.range_zero, Finset.empty_product, Finset.filter_empty, Finset.card_empty]
  | succ n ih =>
    have hsplit : (Finset.range (n + 1) ×ˢ Finset.range k).filter (fun p => R p.1 p.2) =
        (Finset.range n ×ˢ Finset.range k).filter (fun p => R p.1 p.2) ∪
          ((Finset.range k).filter (R n)).image (fun y => (n, y)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, hb⟩, hR⟩
        by_cases han : a < n
        · exact Or.inl ⟨⟨han, hb⟩, hR⟩
        · obtain rfl : a = n := by omega
          exact Or.inr ⟨b, ⟨hb, hR⟩, rfl, rfl⟩
      · rintro (⟨⟨ha, hb⟩, hR⟩ | ⟨y, ⟨hy, hR⟩, rfl, rfl⟩)
        · exact ⟨⟨by omega, hb⟩, hR⟩
        · exact ⟨⟨by omega, hy⟩, hR⟩
    have hdisj : Disjoint ((Finset.range n ×ˢ Finset.range k).filter (fun p => R p.1 p.2))
        (((Finset.range k).filter (R n)).image (fun y => (n, y))) := by
      rw [Finset.disjoint_left]
      rintro ⟨a, b⟩ h1 h2
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
        Prod.mk.injEq] at h1 h2
      obtain ⟨y, -, rfl, -⟩ := h2
      omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun y1 y2 h => (Prod.mk.inj h).2), ih,
      card_range_filter, S_succ]

def G (M m : ℕ) : ℕ :=
  S m (fun x => S m (fun y => if x ^ 3 + y ^ 3 ≡ 1 [MOD M] then 1 else 0))

theorem a_eq (n : ℕ) : a n = G n n := by
  unfold G
  refine Eq.trans ?_ (card_prod_filter n n (fun x y => x ^ 3 + y ^ 3 ≡ 1 [MOD n]))
  unfold a
  apply Finset.card_bij (fun p _ => ((p.1 : ℕ), (p.2 : ℕ)))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨p.1.isLt, p.2.isLt⟩, hp⟩
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hb
    refine ⟨(⟨b.1, hb.1.1⟩, ⟨b.2, hb.1.2⟩), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hb.2

theorem cube_expand (i m x : ℕ) :
    (i * (3 * m) + x) ^ 3 = x ^ 3 + 9 * m * (i * x ^ 2 + 3 * (i ^ 2 * m * x + i ^ 3 * m ^ 2)) := by
  grind

theorem shift_mod (i m x : ℕ) : (i * (3 * m) + x) ^ 3 ≡ x ^ 3 [MOD 9 * m] := by
  unfold Nat.ModEq
  rw [cube_expand, Nat.add_mul_mod_self_left]

theorem lift9 (m : ℕ) : G (9 * m) (9 * m) = 9 * G (9 * m) (3 * m) := by
  unfold G
  rw [split2 (3 * m) (9 * m) (by omega), ← S_mul]
  refine S_congr fun x _ => ?_
  rw [← S_mul]
  refine S_congr fun y _ => ?_
  have h : ∀ i j, (i * (3 * m) + x) ^ 3 + (j * (3 * m) + y) ^ 3 ≡ 1 [MOD 9 * m] ↔
      x ^ 3 + y ^ 3 ≡ 1 [MOD 9 * m] := fun i j =>
    ⟨fun h => ((shift_mod i m x).add (shift_mod j m y)).symm.trans h,
     fun h => ((shift_mod i m x).add (shift_mod j m y)).trans h⟩
  simp only [h]
  rw [S_const, S_const]
  omega

theorem fin_check : ∀ Q < 3, ∀ X < 3, ∀ Y < 3, ¬ (X = 0 ∧ Y = 0) →
    S 3 (fun i => S 3 (fun j => if (Q + i * X ^ 2 + j * Y ^ 2) % 3 = 0 then 1 else 0)) = 3 := by
  decide

theorem local_count (m x y : ℕ) (hm : 0 < m) :
    S 3 (fun i => S 3 (fun j =>
      if (i * (3 * m) + x) ^ 3 + (j * (3 * m) + y) ^ 3 ≡ 1 [MOD 27 * m] then 1 else 0)) =
      3 * (if x ^ 3 + y ^ 3 ≡ 1 [MOD 9 * m] then 1 else 0) := by
  by_cases hP : x ^ 3 + y ^ 3 ≡ 1 [MOD 9 * m]
  · rw [if_pos hP, Nat.mul_one]
    have hA : (x ^ 3 + y ^ 3) % (9 * m) = 1 := by
      have h1 : 1 % (9 * m) = 1 := Nat.mod_eq_of_lt (by omega)
      have := hP
      unfold Nat.ModEq at this
      rw [this, h1]
    have hnot : ¬ (x % 3 = 0 ∧ y % 3 = 0) := by
      rintro ⟨hx, hy⟩
      have h9 : (x ^ 3 + y ^ 3) % 9 = 1 := by
        rw [← Nat.mod_mod_of_dvd (x ^ 3 + y ^ 3) (Nat.dvd_mul_right 9 m), hA]
      obtain ⟨u, rfl⟩ : 3 ∣ x := Nat.dvd_of_mod_eq_zero hx
      obtain ⟨v, rfl⟩ : 3 ∣ y := Nat.dvd_of_mod_eq_zero hy
      have e : (3 * u) ^ 3 + (3 * v) ^ 3 = 9 * (3 * (u ^ 3 + v ^ 3)) := by grind
      rw [e, Nat.mul_mod_right] at h9
      omega
    obtain ⟨q, hq⟩ : ∃ q, (x ^ 3 + y ^ 3) / (9 * m) = q := ⟨_, rfl⟩
    have key : ∀ i j, ((i * (3 * m) + x) ^ 3 + (j * (3 * m) + y) ^ 3 ≡ 1 [MOD 27 * m] ↔
        (q % 3 + i * (x % 3) ^ 2 + j * (y % 3) ^ 2) % 3 = 0) := by
      intro i j
      obtain ⟨N, hN⟩ : ∃ N, N = i * x ^ 2 + j * y ^ 2 +
          3 * (i ^ 2 * m * x + i ^ 3 * m ^ 2 + (j ^ 2 * m * y + j ^ 3 * m ^ 2)) := ⟨_, rfl⟩
      have e : (i * (3 * m) + x) ^ 3 + (j * (3 * m) + y) ^ 3 = (x ^ 3 + y ^ 3) + 9 * m * N := by
        rw [hN, cube_expand, cube_expand]
        grind
      have h27 : 1 % (27 * m) = 1 := Nat.mod_eq_of_lt (by omega)
      have hmod : ((x ^ 3 + y ^ 3) + 9 * m * N) % (27 * m) = 1 + 9 * m * ((q + N) % 3) := by
        rw [show 27 * m = 9 * m * 3 by omega, Nat.mod_mul, Nat.add_mul_mod_self_left, hA,
          Nat.add_mul_div_left (x ^ 3 + y ^ 3) N (show 0 < 9 * m by omega), hq]
      have h1 : q + N ≡ q + i * x ^ 2 + j * y ^ 2 [MOD 3] := by
        unfold Nat.ModEq
        rw [show q + N = q + i * x ^ 2 + j * y ^ 2 +
          3 * (i ^ 2 * m * x + i ^ 3 * m ^ 2 + (j ^ 2 * m * y + j ^ 3 * m ^ 2)) by rw [hN]; omega,
          Nat.add_mul_mod_self_left]
      have h2 : q + i * x ^ 2 + j * y ^ 2 ≡ q % 3 + i * (x % 3) ^ 2 + j * (y % 3) ^ 2 [MOD 3] :=
        ((Nat.mod_modEq q 3).symm.add (((Nat.mod_modEq x 3).symm.pow 2).mul_left i)).add
          (((Nat.mod_modEq y 3).symm.pow 2).mul_left j)
      have h3 : (q + N) % 3 = (q % 3 + i * (x % 3) ^ 2 + j * (y % 3) ^ 2) % 3 := h1.trans h2
      unfold Nat.ModEq
      rw [e, hmod, h27, ← h3]
      constructor
      · intro h
        have h' : 9 * m * ((q + N) % 3) = 0 :=
          Nat.add_left_cancel (h.trans (Nat.add_zero 1).symm)
        rcases Nat.mul_eq_zero.mp h' with h'' | h''
        · omega
        · exact h''
      · intro h
        rw [h, Nat.mul_zero, Nat.add_zero]
    simp only [key]
    exact fin_check (q % 3) (Nat.mod_lt _ (by omega)) (x % 3) (Nat.mod_lt _ (by omega))
      (y % 3) (Nat.mod_lt _ (by omega)) hnot
  · rw [if_neg hP, Nat.mul_zero]
    have h0 : ∀ i j, ¬ ((i * (3 * m) + x) ^ 3 + (j * (3 * m) + y) ^ 3 ≡ 1 [MOD 27 * m]) := by
      intro i j h
      apply hP
      have h' : (i * (3 * m) + x) ^ 3 + (j * (3 * m) + y) ^ 3 ≡ 1 [MOD 9 * m] :=
        Nat.ModEq.of_mul_right 3 (by rw [show 9 * m * 3 = 27 * m by omega]; exact h)
      exact ((shift_mod i m x).add (shift_mod j m y)).symm.trans h'
    simp only [h0, ↓reduceIte]
    rw [S_const, S_const]

theorem lift27 (m : ℕ) (hm : 0 < m) : G (27 * m) (9 * m) = 3 * G (9 * m) (3 * m) := by
  unfold G
  rw [split2 (3 * m) (9 * m) (by omega), ← S_mul]
  refine S_congr fun x _ => ?_
  rw [← S_mul]
  refine S_congr fun y _ => ?_
  exact local_count m x y hm

theorem step (m : ℕ) (hm : 0 < m) : a (27 * m) = 3 * a (9 * m) := by
  rw [a_eq, a_eq]
  have h1 := lift9 (3 * m)
  rw [show 9 * (3 * m) = 27 * m by omega, show 3 * (3 * m) = 9 * m by omega] at h1
  rw [h1, lift27 m hm, lift9 m]
  omega

theorem base : a 9 = 18 := by
  decide +kernel

end R087412

theorem OMA.solution : type_of% @OMA.S_oeis_a087412.main := by
  intro e he
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
  clear he
  induction k with
  | zero => exact R087412.base
  | succ k ih =>
    have h1 : (3 : ℕ) ^ (k + 1 + 2) = 27 * 3 ^ k := by
      rw [Nat.pow_add, Nat.pow_two, Nat.pow_succ]
      omega
    have h2 : (3 : ℕ) ^ (k + 2) = 9 * 3 ^ k := by
      rw [Nat.pow_add, Nat.pow_two]
      omega
    have hpos : 0 < 3 ^ k := Nat.pow_pos (by decide)
    rw [h2] at ih
    rw [h1, R087412.step (3 ^ k) hpos, ih]
    omega
