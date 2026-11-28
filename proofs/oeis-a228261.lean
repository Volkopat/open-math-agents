import OMAStatements.S_oeis_a228261

/-!
OEIS A228261 (R. H. Hardin, Aug 19 2013): Number of third differences of arrays of length 5 of numbers in 0..n.
Conjectures from Colin Barker, Sep 10 2018: G.f.: x*(31 + 50*x - 17*x^2 + 6*x^3) / (1 - x)^3. a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>4.

Proof. The pair of third differences of x is (a, b) = (x3 - 3x2 + 3x1 - x0, x4 - 3x3 + 3x2 - x1).
For n >= 2 the pairs are exactly the lattice points of the decagon |a| <= 4n, |b| <= 4n,
|a + b| <= 3n, |a + 3b| <= 9n, |3a + b| <= 9n, except the points with a + b = 3n or -3n and
a not divisible by 3, with a + b = 3n - 1 and a = 1 mod 3, and with a + b = 1 - 3n and a = 2 mod 3
(`Tp`). Every pair satisfies these conditions by linear arithmetic (`img_sub`). Conversely, the
decagon for n is the decagon for n - 1 plus the one for n = 1, and a point of the set for n + 1,
moved back by the vertex of the n = 1 decagon whose angular sector holds it, lies in the set for n
(`step`, ten sectors bounded by the sums of consecutive vertices); adding the matching array of
zeros and ones gives an array for n + 1 from one for n (`img_sup`), starting from an explicit table
for n = 2 checked by evaluation (`base_table`). Counting the set by the slices a + b = s gives
a(n) = 35n^2 + n + 1 for n >= 2 (`card_T`), and a(1) = 31 is computed directly; the g.f. and the
recurrence follow by comparing coefficients.
-/

namespace OMA.S_oeis_a228261

open PowerSeries Finset


/-- The two third differences as a pair. -/
def pr (v : Fin 2 → ℤ) : ℤ × ℤ := (v 0, v 1)

lemma pr_inj : Function.Injective pr := by
  intro v w h
  simp only [pr, Prod.mk.injEq] at h
  funext i
  fin_cases i
  · exact h.1
  · exact h.2

lemma a_eq (n : ℕ) :
    a n = ((univ : Finset (Fin 5 → Fin (n + 1))).image (fun x => pr (thirdDiff x))).card := by
  unfold a
  rw [show (fun x : Fin 5 → Fin (n + 1) => pr (thirdDiff x)) = pr ∘ thirdDiff from rfl,
    ← Finset.image_image, card_image_of_injective _ pr_inj]

lemma td {N : ℕ} (x : Fin 5 → Fin N) :
    pr (thirdDiff x) = ((x 3 : ℤ) - 3 * (x 2 : ℤ) + 3 * (x 1 : ℤ) - (x 0 : ℤ),
      (x 4 : ℤ) - 3 * (x 3 : ℤ) + 3 * (x 2 : ℤ) - (x 1 : ℤ)) := rfl

/-- The pairs of third differences for n >= 2: the decagon without 6n points next to the edges
a + b = 3n and a + b = -3n. -/
def Tp (n : ℕ) (a b : ℤ) : Prop :=
  -4 * (n : ℤ) ≤ a ∧ a ≤ 4 * n ∧ -4 * (n : ℤ) ≤ b ∧ b ≤ 4 * n ∧
  -3 * (n : ℤ) ≤ a + b ∧ a + b ≤ 3 * n ∧
  -9 * (n : ℤ) ≤ a + 3 * b ∧ a + 3 * b ≤ 9 * n ∧
  -9 * (n : ℤ) ≤ 3 * a + b ∧ 3 * a + b ≤ 9 * n ∧
  (a + b = 3 * n → a % 3 = 0) ∧ (a + b = -3 * n → a % 3 = 0) ∧
  (a + b = 3 * n - 1 → a % 3 ≠ 1) ∧ (a + b = 1 - 3 * n → a % 3 ≠ 2)

instance (n : ℕ) (a b : ℤ) : Decidable (Tp n a b) := by unfold Tp; infer_instance

lemma img_sub {n : ℕ} (x : Fin 5 → Fin (n + 1)) :
    Tp n (pr (thirdDiff x)).1 (pr (thirdDiff x)).2 := by
  rw [td]
  dsimp only
  have b0 := (x 0).isLt
  have b1 := (x 1).isLt
  have b2 := (x 2).isLt
  have b3 := (x 3).isLt
  have b4 := (x 4).isLt
  unfold Tp
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, ?_, ?_, ?_, ?_⟩
  · intro h
    have e1 : ((x 1 : ℕ) : ℤ) = n := by omega
    have e3 : ((x 3 : ℕ) : ℤ) = 0 := by omega
    have e0 : ((x 0 : ℕ) : ℤ) = 0 := by omega
    rw [e1, e3, e0]
    omega
  · intro h
    have e1 : ((x 1 : ℕ) : ℤ) = 0 := by omega
    have e3 : ((x 3 : ℕ) : ℤ) = n := by omega
    have e0 : ((x 0 : ℕ) : ℤ) = n := by omega
    rw [e1, e3, e0]
    omega
  · intro h
    have e1 : ((x 1 : ℕ) : ℤ) = n := by omega
    have e3 : ((x 3 : ℕ) : ℤ) = 0 := by omega
    have e0 : ((x 0 : ℕ) : ℤ) = 0 ∨ ((x 0 : ℕ) : ℤ) = 1 := by omega
    rcases e0 with e0 | e0 <;> rw [e1, e3, e0] <;> omega
  · intro h
    have e1 : ((x 1 : ℕ) : ℤ) = 0 := by omega
    have e3 : ((x 3 : ℕ) : ℤ) = n := by omega
    have e0 : ((x 0 : ℕ) : ℤ) = n - 1 ∨ ((x 0 : ℕ) : ℤ) = n := by omega
    rcases e0 with e0 | e0 <;> rw [e1, e3, e0] <;> omega

/-! The arrays for n = 2, as base-3 codes of the five entries, indexed by (a + 8, b + 8). -/

/-- The code of an array of numbers in 0..2 with third differences (i - 8, j - 8). -/
def code2 : Fin 17 → Fin 17 → ℕ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 101, 182],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 128, 209, 19, 100, 181],
    ![0, 0, 0, 0, 0, 0, 0, 0, 74, 155, 236, 46, 127, 208, 18, 99, 180],
    ![0, 0, 0, 0, 0, 0, 0, 0, 73, 154, 235, 45, 126, 207, 104, 185, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 72, 153, 234, 10, 91, 172, 103, 184, 0],
    ![0, 0, 0, 0, 0, 65, 146, 227, 37, 118, 199, 9, 90, 171, 102, 183, 0],
    ![0, 0, 0, 0, 0, 64, 145, 226, 36, 117, 198, 129, 210, 107, 188, 0, 0],
    ![0, 0, 0, 0, 0, 63, 144, 225, 156, 237, 163, 94, 175, 106, 187, 0, 0],
    ![0, 0, 56, 137, 218, 28, 109, 190, 0, 81, 162, 93, 174, 105, 186, 0, 0],
    ![0, 0, 55, 136, 217, 27, 108, 189, 120, 201, 132, 213, 0, 0, 0, 0, 0],
    ![0, 0, 54, 135, 216, 147, 228, 159, 240, 166, 97, 178, 0, 0, 0, 0, 0],
    ![0, 59, 140, 221, 31, 112, 193, 3, 84, 165, 96, 177, 0, 0, 0, 0, 0],
    ![0, 58, 139, 220, 30, 111, 192, 123, 204, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 57, 138, 219, 150, 231, 7, 88, 169, 0, 0, 0, 0, 0, 0, 0, 0],
    ![62, 143, 224, 34, 115, 196, 6, 87, 168, 0, 0, 0, 0, 0, 0, 0, 0],
    ![61, 142, 223, 33, 114, 195, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![60, 141, 222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The array with code `code2 i j`: entry k is digit k in base 3. -/
def w2 (i j : Fin 17) : Fin 5 → Fin 3 :=
  fun k => ⟨code2 i j / 3 ^ (k : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩

lemma base_table : ∀ i j : Fin 17, Tp 2 ((i : ℤ) - 8) ((j : ℤ) - 8) →
    pr (thirdDiff (w2 i j)) = ((i : ℤ) - 8, (j : ℤ) - 8) := by
  decide +kernel

/-! From n to n + 1. -/

/-- The vertices of the decagon for n = 1. -/
def vset : Finset (ℤ × ℤ) :=
  {(0, -3), (3, -4), (4, -4), (4, -3), (3, 0), (0, 3), (-3, 4), (-4, 4), (-4, 3), (-3, 0)}

lemma vwit : ∀ v ∈ vset, ∃ e : Fin 5 → Fin 2, pr (thirdDiff e) = v := by
  intro v hv
  simp only [vset, mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨![1, 0, 0, 1, 0], by decide⟩, ⟨![1, 1, 0, 1, 0], by decide⟩, ⟨![0, 1, 0, 1, 0], by decide⟩,
    ⟨![0, 1, 0, 1, 1], by decide⟩, ⟨![0, 1, 0, 0, 1], by decide⟩, ⟨![0, 1, 1, 0, 1], by decide⟩,
    ⟨![0, 0, 1, 0, 1], by decide⟩, ⟨![1, 0, 1, 0, 1], by decide⟩, ⟨![1, 0, 1, 0, 0], by decide⟩,
    ⟨![1, 0, 1, 1, 0], by decide⟩]

/-- The sector of a point among the rays through the sums of consecutive vertices, (3, -7),
(7, -8), (8, -7), (7, -3), (3, 3) and their opposites, picks the vertex to move it back by. -/
lemma step (n : ℕ) (hn : 2 ≤ n) (a b : ℤ) (h : Tp (n + 1) a b) :
    ∃ v ∈ vset, Tp n (a - v.1) (b - v.2) := by
  unfold Tp at h ⊢
  push_cast at h
  rcases le_total b a with hab | hab
  · rcases le_total 0 (7 * b + 8 * a) with h1 | h1
    · rcases le_total 0 (7 * b + 3 * a) with h2 | h2
      · exact ⟨(3, 0), by simp [vset], by dsimp only; omega⟩
      · rcases le_total 0 (8 * b + 7 * a) with h3 | h3
        · exact ⟨(4, -3), by simp [vset], by dsimp only; omega⟩
        · exact ⟨(4, -4), by simp [vset], by dsimp only; omega⟩
    · rcases le_total 0 (3 * b + 7 * a) with h2 | h2
      · exact ⟨(3, -4), by simp [vset], by dsimp only; omega⟩
      · exact ⟨(0, -3), by simp [vset], by dsimp only; omega⟩
  · rcases le_total (7 * b + 8 * a) 0 with h1 | h1
    · rcases le_total (7 * b + 3 * a) 0 with h2 | h2
      · exact ⟨(-3, 0), by simp [vset], by dsimp only; omega⟩
      · rcases le_total (8 * b + 7 * a) 0 with h3 | h3
        · exact ⟨(-4, 3), by simp [vset], by dsimp only; omega⟩
        · exact ⟨(-4, 4), by simp [vset], by dsimp only; omega⟩
    · rcases le_total (3 * b + 7 * a) 0 with h2 | h2
      · exact ⟨(-3, 4), by simp [vset], by dsimp only; omega⟩
      · exact ⟨(0, 3), by simp [vset], by dsimp only; omega⟩

lemma img_sup (n : ℕ) (hn : 2 ≤ n) : ∀ a b : ℤ, Tp n a b →
    ∃ x : Fin 5 → Fin (n + 1), pr (thirdDiff x) = (a, b) := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro a b h
    have hb : -8 ≤ a ∧ a ≤ 8 ∧ -8 ≤ b ∧ b ≤ 8 := by
      unfold Tp at h
      push_cast at h
      omega
    obtain ⟨i, hi⟩ : ∃ i : Fin 17, (i : ℤ) - 8 = a :=
      ⟨⟨(a + 8).toNat, by omega⟩, by simp only; omega⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin 17, (j : ℤ) - 8 = b :=
      ⟨⟨(b + 8).toNat, by omega⟩, by simp only; omega⟩
    subst hi hj
    exact ⟨w2 i j, base_table i j h⟩
  | succ n hn ih =>
    intro a b h
    obtain ⟨⟨v1, v2⟩, hv, hT⟩ := step n hn a b h
    obtain ⟨x, hx⟩ := ih _ _ hT
    obtain ⟨e, he⟩ := vwit _ hv
    refine ⟨fun i => ⟨(x i : ℕ) + (e i : ℕ), by have := (x i).isLt; have := (e i).isLt; omega⟩, ?_⟩
    rw [td] at hx he ⊢
    simp only [Prod.mk.injEq] at hx he ⊢
    push_cast
    constructor <;> linarith [hx.1, hx.2, he.1, he.2]

/-- The set of pairs for n >= 2. -/
noncomputable def Tset (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-4 * (n : ℤ)) (4 * n)) ×ˢ (Icc (-4 * (n : ℤ)) (4 * n))).filter (fun p => Tp n p.1 p.2)

lemma img_eq (n : ℕ) (hn : 2 ≤ n) :
    (univ : Finset (Fin 5 → Fin (n + 1))).image (fun x => pr (thirdDiff x)) = Tset n := by
  ext ⟨p1, p2⟩
  simp only [mem_image, mem_univ, true_and, Tset, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨x, hx⟩
    have h := img_sub x
    rw [hx] at h
    dsimp only at h
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, h⟩ <;> unfold Tp at h <;> omega
  · rintro ⟨-, h⟩
    exact img_sup n hn p1 p2 h

/-! Counting by the slices a + b = s. -/

/-- The least a of the slice a + b = s of the decagon. -/
def lo (n : ℕ) (s : ℤ) : ℤ :=
  max (max (-4 * (n : ℤ)) (s - 4 * n)) (max (-((9 * n - 3 * s) / 2)) (-((9 * n + s) / 2)))

/-- The largest a of the slice a + b = s of the decagon. -/
def hi (n : ℕ) (s : ℤ) : ℤ :=
  min (min (4 * (n : ℤ)) (s + 4 * n)) (min ((3 * s + 9 * n) / 2) ((9 * n - s) / 2))

/-- The size of the slice a + b = s of the decagon. -/
def W (n : ℕ) (s : ℤ) : ℤ := hi n s + 1 - lo n s

lemma fiber (n : ℕ) (s : ℤ) (hs1 : -3 * (n : ℤ) + 2 ≤ s) (hs2 : s ≤ 3 * n - 2) :
    (Tset n).filter (fun p => p.1 + p.2 = s) = (Icc (lo n s) (hi n s)).image (fun a => (a, s - a)) := by
  ext ⟨p1, p2⟩
  simp only [Tset, mem_filter, mem_product, mem_Icc, mem_image, Prod.mk.injEq]
  unfold Tp lo hi
  constructor
  · rintro ⟨⟨_, h⟩, hs⟩
    exact ⟨p1, by omega, rfl, by omega⟩
  · rintro ⟨a, ha, rfl, rfl⟩
    omega

lemma card_fiber (n : ℕ) (s : ℤ) (hs1 : -3 * (n : ℤ) + 2 ≤ s) (hs2 : s ≤ 3 * n - 2) :
    (((Tset n).filter (fun p => p.1 + p.2 = s)).card : ℤ) = W n s := by
  rw [fiber n s hs1 hs2, card_image_of_injective _ (fun a a' h => (Prod.mk.inj h).1), Int.card_Icc]
  unfold W lo hi
  rw [Int.toNat_of_nonneg (by omega)]

lemma fib_top (n : ℕ) (s : ℤ) (hs : s = 3 * n) :
    ((Tset n).filter (fun p => p.1 + p.2 = s)).card = n + 1 := by
  subst hs
  have e : (Tset n).filter (fun p : ℤ × ℤ => p.1 + p.2 = 3 * (n : ℤ)) =
      (range (n + 1)).image (fun k : ℕ => (3 * (k : ℤ), 3 * (n : ℤ) - 3 * k)) := by
    ext ⟨p1, p2⟩
    simp only [Tset, mem_filter, mem_product, mem_Icc, mem_image, mem_range, Prod.mk.injEq]
    unfold Tp
    constructor
    · rintro ⟨⟨_, h⟩, hs⟩
      exact ⟨(p1 / 3).toNat, by omega, by omega, by omega⟩
    · rintro ⟨k, hk, rfl, rfl⟩
      omega
  rw [e, card_image_of_injective _ (fun k k' h => by simp only [Prod.mk.injEq] at h; omega),
    card_range]

lemma fib_bot (n : ℕ) (s : ℤ) (hs : s = -3 * n) :
    ((Tset n).filter (fun p => p.1 + p.2 = s)).card = n + 1 := by
  subst hs
  have e : (Tset n).filter (fun p : ℤ × ℤ => p.1 + p.2 = -3 * (n : ℤ)) =
      (range (n + 1)).image (fun k : ℕ => (-3 * (k : ℤ), -3 * (n : ℤ) + 3 * k)) := by
    ext ⟨p1, p2⟩
    simp only [Tset, mem_filter, mem_product, mem_Icc, mem_image, mem_range, Prod.mk.injEq]
    unfold Tp
    constructor
    · rintro ⟨⟨_, h⟩, hs⟩
      exact ⟨(-p1 / 3).toNat, by omega, by omega, by omega⟩
    · rintro ⟨k, hk, rfl, rfl⟩
      omega
  rw [e, card_image_of_injective _ (fun k k' h => by simp only [Prod.mk.injEq] at h; omega),
    card_range]

lemma fib_top1 (n : ℕ) (hn : 1 ≤ n) (s : ℤ) (hs : s = 3 * n - 1) :
    ((Tset n).filter (fun p => p.1 + p.2 = s)).card = 2 * n + 2 := by
  subst hs
  have e : (Tset n).filter (fun p : ℤ × ℤ => p.1 + p.2 = 3 * (n : ℤ) - 1) =
      (range (2 * n + 2)).image (fun k : ℕ => (3 * ((k : ℤ) / 2) - 1 + (k : ℤ) % 2,
        3 * (n : ℤ) - 1 - (3 * ((k : ℤ) / 2) - 1 + (k : ℤ) % 2))) := by
    ext ⟨p1, p2⟩
    simp only [Tset, mem_filter, mem_product, mem_Icc, mem_image, mem_range, Prod.mk.injEq]
    unfold Tp
    constructor
    · rintro ⟨⟨_, h⟩, hs⟩
      exact ⟨((2 * p1 + 3) / 3).toNat, by omega, by omega, by omega⟩
    · rintro ⟨k, hk, rfl, rfl⟩
      omega
  rw [e, card_image_of_injective _ (fun k k' h => by simp only [Prod.mk.injEq] at h; omega),
    card_range]

lemma fib_bot1 (n : ℕ) (hn : 1 ≤ n) (s : ℤ) (hs : s = 1 - 3 * n) :
    ((Tset n).filter (fun p => p.1 + p.2 = s)).card = 2 * n + 2 := by
  subst hs
  have e : (Tset n).filter (fun p : ℤ × ℤ => p.1 + p.2 = 1 - 3 * (n : ℤ)) =
      (range (2 * n + 2)).image (fun k : ℕ => (-(3 * ((k : ℤ) / 2) - 1 + (k : ℤ) % 2),
        1 - 3 * (n : ℤ) + (3 * ((k : ℤ) / 2) - 1 + (k : ℤ) % 2))) := by
    ext ⟨p1, p2⟩
    simp only [Tset, mem_filter, mem_product, mem_Icc, mem_image, mem_range, Prod.mk.injEq]
    unfold Tp
    constructor
    · rintro ⟨⟨_, h⟩, hs⟩
      have hm : p1 % 3 = 0 ∨ p1 % 3 = 1 := by omega
      rcases hm with hm | hm
      · exact ⟨(2 * (-p1 / 3) + 1).toNat, by omega, by omega, by omega⟩
      · exact ⟨(2 * ((1 - p1) / 3)).toNat, by omega, by omega, by omega⟩
    · rintro ⟨k, hk, rfl, rfl⟩
      omega
  rw [e, card_image_of_injective _ (fun k k' h => by simp only [Prod.mk.injEq] at h; omega),
    card_range]

lemma sum_Ico_one (f : ℕ → ℤ) (a b : ℕ) (h : b = a + 1) : ∑ i ∈ Ico a b, f i = f a := by
  subst h
  rw [Nat.Ico_succ_singleton, sum_singleton]

lemma parity_count (n : ℕ) :
    ∑ j ∈ range (2 * n + 1), (if j % 2 = 0 then (1 : ℤ) else 0) = n + 1 := by
  induction n with
  | zero => rw [show 2 * 0 + 1 = 1 by rfl, sum_range_one]; simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    rw [if_neg (by omega), if_pos (by omega)]
    push_cast
    ring

lemma card_T (n : ℕ) (hn : 2 ≤ n) : ((Tset n).card : ℤ) = 35 * n ^ 2 + n + 1 := by
  rw [card_eq_sum_card_fiberwise (f := fun p : ℤ × ℤ => p.1 + p.2) (t := Icc (-3 * (n : ℤ)) (3 * n))
    (by
      intro p hp
      simp only [Tset, coe_filter, mem_product, mem_Icc, Set.mem_ofPred_eq] at hp
      unfold Tp at hp
      simp only [coe_Icc, Set.mem_Icc]
      omega)]
  push_cast
  rw [Int.Icc_eq_finset_map, sum_map]
  rw [show (3 * (n : ℤ) + 1 - -3 * n).toNat = 6 * n + 1 by omega]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le 1) (show 1 ≤ 6 * n + 1 by omega),
    ← sum_Ico_consecutive _ (show 1 ≤ 2 by omega) (show 2 ≤ 6 * n + 1 by omega),
    ← sum_Ico_consecutive _ (show 2 ≤ 2 * n + 1 by omega) (show 2 * n + 1 ≤ 6 * n + 1 by omega),
    ← sum_Ico_consecutive _ (show 2 * n + 1 ≤ 3 * n by omega) (show 3 * n ≤ 6 * n + 1 by omega),
    ← sum_Ico_consecutive _ (show 3 * n ≤ 3 * n + 1 by omega) (show 3 * n + 1 ≤ 6 * n + 1 by omega),
    ← sum_Ico_consecutive _ (show 3 * n + 1 ≤ 4 * n by omega) (show 4 * n ≤ 6 * n + 1 by omega),
    ← sum_Ico_consecutive _ (show 4 * n ≤ 6 * n - 1 by omega) (show 6 * n - 1 ≤ 6 * n + 1 by omega),
    ← sum_Ico_consecutive _ (show 6 * n - 1 ≤ 6 * n by omega) (show 6 * n ≤ 6 * n + 1 by omega)]
  rw [sum_Ico_one _ 0 1 rfl, sum_Ico_one _ 1 2 rfl, sum_Ico_one _ (3 * n) (3 * n + 1) rfl,
    sum_Ico_one _ (6 * n - 1) (6 * n) (by omega), sum_Ico_one _ (6 * n) (6 * n + 1) rfl]
  rw [fib_bot n _ (by norm_num), fib_bot1 n (by omega) _ (by push_cast; ring),
    card_fiber n _ (by push_cast; omega) (by push_cast; omega),
    fib_top1 n (by omega) _ (by omega), fib_top n _ (by push_cast; ring)]
  rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range, sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
  rw [show 2 * n + 1 - 2 = 2 * n - 1 by omega, show 3 * n - (2 * n + 1) = n - 1 by omega,
    show 4 * n - (3 * n + 1) = n - 1 by omega, show 6 * n - 1 - 4 * n = 2 * n - 1 by omega]
  have hW0 : W n (-3 * n + ((3 * n : ℕ) : ℤ)) = 8 * n + 1 := by
    unfold W lo hi
    push_cast
    omega
  have b2 : ∀ j ∈ range (2 * n - 1),
      ((((Tset n).filter (fun p => p.1 + p.2 = -3 * n + ((2 + j : ℕ) : ℤ))).card : ℕ) : ℤ) =
        3 * n + 4 + 2 * j + (if j % 2 = 0 then 1 else 0) := by
    intro j hj
    rw [mem_range] at hj
    rw [card_fiber n _ (by push_cast; omega) (by push_cast; omega)]
    unfold W lo hi
    push_cast
    split_ifs <;> omega
  have b3 : ∀ j ∈ range (n - 1),
      ((((Tset n).filter (fun p => p.1 + p.2 = -3 * n + ((2 * n + 1 + j : ℕ) : ℤ))).card : ℕ) : ℤ) =
        7 * n + 2 + j := by
    intro j hj
    rw [mem_range] at hj
    rw [card_fiber n _ (by push_cast; omega) (by push_cast; omega)]
    unfold W lo hi
    push_cast
    omega
  have b5 : ∀ j ∈ range (n - 1),
      ((((Tset n).filter (fun p => p.1 + p.2 = -3 * n + ((3 * n + 1 + j : ℕ) : ℤ))).card : ℕ) : ℤ) =
        8 * n - j := by
    intro j hj
    rw [mem_range] at hj
    rw [card_fiber n _ (by push_cast; omega) (by push_cast; omega)]
    unfold W lo hi
    push_cast
    omega
  have b6 : ∀ j ∈ range (2 * n - 1),
      ((((Tset n).filter (fun p => p.1 + p.2 = -3 * n + ((4 * n + j : ℕ) : ℤ))).card : ℕ) : ℤ) =
        7 * n - 2 * j + (if j % 2 = 0 then 1 else 0) := by
    intro j hj
    rw [mem_range] at hj
    rw [card_fiber n _ (by push_cast; omega) (by push_cast; omega)]
    unfold W lo hi
    push_cast
    split_ifs <;> omega
  rw [sum_congr rfl b2, sum_congr rfl b3, sum_congr rfl b5, sum_congr rfl b6, hW0]
  have hpar : ∑ j ∈ range (2 * n - 1), (if j % 2 = 0 then (1 : ℤ) else 0) = n := by
    rw [show 2 * n - 1 = 2 * (n - 1) + 1 by omega, parity_count]
    push_cast [show 1 ≤ n by omega]
    ring
  have h26 : ∑ j ∈ range (2 * n - 1), ((3 : ℤ) * n + 4 + 2 * j + (if j % 2 = 0 then 1 else 0)) +
      ∑ j ∈ range (2 * n - 1), ((7 : ℤ) * n - 2 * j + (if j % 2 = 0 then 1 else 0)) =
      (2 * n - 1) * (10 * n + 4) + 2 * n := by
    rw [← sum_add_distrib]
    have hs : ∀ j ∈ range (2 * n - 1),
        ((3 : ℤ) * n + 4 + 2 * (j : ℤ) + (if j % 2 = 0 then 1 else 0)) +
          ((7 : ℤ) * n - 2 * (j : ℤ) + (if j % 2 = 0 then 1 else 0)) =
        (10 * n + 4) + 2 * (if j % 2 = 0 then (1 : ℤ) else 0) := fun j _ => by ring
    rw [sum_congr rfl hs, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum, hpar]
    push_cast [show 1 ≤ 2 * n by omega]
    ring
  have h35 : ∑ j ∈ range (n - 1), ((7 : ℤ) * n + 2 + j) + ∑ j ∈ range (n - 1), ((8 : ℤ) * n - j) =
      (n - 1) * (15 * n + 2) := by
    rw [← sum_add_distrib]
    have hs : ∀ j ∈ range (n - 1), ((7 : ℤ) * n + 2 + (j : ℤ)) + ((8 : ℤ) * n - (j : ℤ)) = 15 * n + 2 :=
      fun j _ => by ring
    rw [sum_congr rfl hs, sum_const, card_range, nsmul_eq_mul]
    push_cast [show 1 ≤ n by omega]
    ring
  push_cast
  linear_combination h26 + h35

lemma a_one : a 1 = 31 := by
  decide +kernel

/-- a(n) as a polynomial in n, for n >= 2. -/
lemma a_poly (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = 35 * (n : ℚ) ^ 2 + n + 1 := by
  have h : (a n : ℤ) = 35 * n ^ 2 + n + 1 := by rw [a_eq, img_eq n hn, card_T n hn]
  exact_mod_cast h

/-- Barker's g.f. -/
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
      X * (31 + 50 * X - 17 * X ^ 2 + 6 * X ^ 3) := by
  have v1 : (a 1 : ℚ) = 31 := by exact_mod_cast a_one
  have v2 : (a 2 : ℚ) = 143 := by rw [a_poly 2 (by norm_num)]; norm_num
  have v3 : (a 3 : ℚ) = 319 := by rw [a_poly 3 (by norm_num)]; norm_num
  have v4 : (a 4 : ℚ) = 565 := by rw [a_poly 4 (by norm_num)]; norm_num
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 3 = A - C (3 : ℚ) * (A * X ^ 1) + C (3 : ℚ) * (A * X ^ 2) - A * X ^ 3 := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (31 + 50 * X - 17 * X ^ 2 + 6 * X ^ 3) : ℚ⟦X⟧) =
      X ^ 1 * C (31 : ℚ) + X ^ 2 * C (50 : ℚ) - X ^ 3 * C (17 : ℚ) + X ^ 4 * C (6 : ℚ) := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk,
    coeff_C_mul]
  rcases n with _ | _ | _ | _ | _ | m
  · simp
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2, v3]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v1, v2, v3, v4]
    all_goals norm_num
  · simp only [show ¬ (m + 5 = 0) by omega, show 1 ≤ m + 5 by omega, show m + 5 - 1 = m + 4 by omega,
      show ¬ (m + 4 = 0) by omega, show 2 ≤ m + 5 by omega, show m + 5 - 2 = m + 3 by omega,
      show ¬ (m + 3 = 0) by omega, show 3 ≤ m + 5 by omega, show m + 5 - 3 = m + 2 by omega,
      show ¬ (m + 2 = 0) by omega, show ¬ (m + 5 = 1) by omega, show ¬ (m + 5 = 2) by omega,
      show ¬ (m + 5 = 3) by omega, show ¬ (m + 5 = 4) by omega, if_true, if_false]
    rw [a_poly (m + 5) (by omega), a_poly (m + 4) (by omega), a_poly (m + 3) (by omega),
      a_poly (m + 2) (by omega)]
    push_cast
    ring

/-- Barker's recurrence. -/
theorem recur : ∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega]
  have h : (a (m + 5) : ℚ) = 3 * a (m + 4) - 3 * a (m + 3) + a (m + 2) := by
    rw [a_poly (m + 5) (by omega), a_poly (m + 4) (by omega), a_poly (m + 3) (by omega),
      a_poly (m + 2) (by omega)]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
      X * (31 + 50 * X - 17 * X ^ 2 + 6 * X ^ 3) ∧
    ∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a228261

theorem OMA.solution : type_of% @OMA.S_oeis_a228261.main :=
  OMA.S_oeis_a228261.conjecture
