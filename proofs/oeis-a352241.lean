import OMAStatements.S_oeis_a352241
import Mathlib

/-!
# Two finite counterexamples to the five formulas for black-square queens

Integer weights on rows, columns and diagonals give an upper bound because
a nonattacking placement uses each line at most once. The kernel checks every
black square against the weights and checks that the displayed placements attain
the resulting bounds. The 52-board is read from Andy Huchala's OEIS illustration,
reflected horizontally to match the zero-based color convention. The 57-board
was found by extending and repairing placements with CP-SAT.
-/
namespace OMA.BlackQueens
open OMA.S_oeis_a352241 Finset

lemma line_cap {α β : Type} [Fintype β] [DecidableEq β] (s : Finset α) (f : α → β)
    (w : β → ℕ) (h : Set.InjOn f (s : Set α)) :
    ∑ p ∈ s, w (f p) ≤ ∑ i, w i := by
  rw [← sum_image h]
  exact sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

theorem weighted_cap {n D : ℕ} (row col : Fin n → ℕ) (up down : Fin (2*n) → ℕ)
    (cover : ∀ p : Square n, (p.1.val+p.2.val)%2 = 0 →
      D ≤ row p.1 + col p.2 + up (sumLine p) + down (diffLine p))
    {s : Finset (Square n)} (hs : valid s) :
    s.card*D ≤ (∑ i, row i) + (∑ i, col i) + (∑ i, up i) + (∑ i, down i) := by
  obtain ⟨hb,hr,hc,hu,hd⟩ := hs
  have hl := sum_le_sum (s := s) (f := fun _ => D)
    (fun p hp => cover p (hb p hp))
  have h1 := line_cap s Prod.fst row hr
  have h2 := line_cap s Prod.snd col hc
  have h3 := line_cap s sumLine up hu
  have h4 := line_cap s diffLine down hd
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,sum_add_distrib] at hl
  omega

lemma valid_of_counts {n : ℕ} (s : Finset (Square n)) (k : ℕ) (hc : s.card=k)
    (h : (∀ p ∈ s, (p.1.val+p.2.val)%2=0) ∧
      (s.image Prod.fst).card=k ∧ (s.image Prod.snd).card=k ∧
      (s.image sumLine).card=k ∧ (s.image diffLine).card=k) : valid s := by
  obtain ⟨hb,h1,h2,h3,h4⟩ := h
  exact ⟨hb,injOn_of_card_image_eq (h1.trans hc.symm),injOn_of_card_image_eq (h2.trans hc.symm),
      injOn_of_card_image_eq (h3.trans hc.symm),injOn_of_card_image_eq (h4.trans hc.symm)⟩

private def row52 (i : Fin 52) : ℕ :=
  (#[3860, 3478, 3115, 2773, 2450, 2157, 1863, 1600, 1356, 1132, 927, 742, 577, 432, 306, 200, 114, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 114, 200, 306, 432, 577, 742, 927, 1132, 1356, 1600, 1863, 2157, 2450, 2773, 3115, 3478, 3860] : Array ℕ)[i.val]!

private def col52 (i : Fin 52) : ℕ :=
  (#[3860, 3478, 3115, 2773, 2450, 2157, 1863, 1600, 1356, 1132, 927, 742, 577, 432, 306, 200, 114, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 114, 200, 306, 432, 577, 742, 927, 1132, 1356, 1600, 1863, 2157, 2450, 2773, 3115, 3478, 3860] : Array ℕ)[i.val]!

private def up52 (i : Fin (2*52)) : ℕ :=
  (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 567, 0, 1095, 0, 1583, 0, 2031, 0, 2440, 0, 2810, 0, 3140, 0, 3431, 0, 3692, 0, 3985, 0, 4278, 0, 4572, 0, 4887, 0, 5163, 0, 5400, 0, 5597, 0, 5755, 0, 5873, 0, 5952, 0, 5991, 0, 5991, 0, 5952, 0, 5873, 0, 5755, 0, 5597, 0, 5400, 0, 5163, 0, 4887, 0, 4572, 0, 4278, 0, 3985, 0, 3692, 0, 3431, 0, 3140, 0, 2810, 0, 2440, 0, 2031, 0, 1583, 0, 1095, 0, 567, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Array ℕ)[i.val]!

private def down52 (i : Fin (2*52)) : ℕ :=
  (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 548, 0, 1055, 0, 1523, 0, 1952, 0, 2342, 0, 2691, 0, 3002, 0, 3273, 0, 3566, 0, 3860, 0, 4153, 0, 4446, 0, 4742, 0, 4998, 0, 5215, 0, 5392, 0, 5530, 0, 5629, 0, 5688, 0, 5708, 0, 5688, 0, 5629, 0, 5530, 0, 5392, 0, 5215, 0, 4998, 0, 4742, 0, 4446, 0, 4153, 0, 3860, 0, 3566, 0, 3273, 0, 3002, 0, 2691, 0, 2342, 0, 1952, 0, 1523, 0, 1055, 0, 548, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Array ℕ)[i.val]!

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem cover52 : ∀ p : Square 52, (p.1.val+p.2.val)%2=0 →
    10000 ≤ row52 p.1 + col52 p.2 + up52 (sumLine p) + down52 (diffLine p) := by decide +kernel

set_option maxRecDepth 10000 in
private theorem cost52 : (∑ i, row52 i) + (∑ i, col52 i) +
    (∑ i, up52 i) + (∑ i, down52 i) = 409918 := by decide +kernel

set_option maxRecDepth 10000 in
theorem cap52 {s : Finset (Square 52)} (hs : valid s) : s.card ≤ 40 := by
  have h := weighted_cap row52 col52 up52 down52 cover52 hs
  have hh := h.trans_eq cost52
  clear h
  omega

private def placement52 : Finset (Square 52) :=
  ([(0,14), (1,23), (2,10), (3,15), (4,38), (5,25), (7,39), (8,48), (10,12), (11,41), (12,36), (13,7), (14,40), (15,51), (16,0), (17,45), (18,16), (20,8), (25,1), (27,5), (28,46), (31,47), (33,3), (34,6), (35,9), (36,2), (37,33), (38,42), (39,21), (40,50), (41,31), (43,49), (44,44), (45,37), (46,4), (47,11), (48,28), (49,35), (50,18), (51,13)] : List (Square 52)).toFinset

set_option maxRecDepth 10000 in
theorem exact52 : IsGreatest {k : ℕ | ∃ s : Finset (Square 52), valid s ∧ s.card=k} 40 := by
  constructor
  · exact ⟨placement52, valid_of_counts placement52 40 (by decide +kernel) (by decide +kernel), by decide +kernel⟩
  · rintro k ⟨s,hs,rfl⟩
    exact cap52 hs

private def row57 (i : Fin 57) : ℕ :=
  (#[3961, 3606, 3268, 2946, 2641, 2352, 2080, 1824, 1585, 1362, 1156, 966, 793, 636, 496, 372, 265, 174, 100, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 100, 174, 265, 372, 496, 636, 793, 966, 1156, 1362, 1585, 1824, 2080, 2352, 2641, 2946, 3268, 3606, 3961] : Array ℕ)[i.val]!

private def col57 (i : Fin 57) : ℕ :=
  (#[3961, 3606, 3268, 2946, 2641, 2352, 2080, 1824, 1585, 1362, 1156, 966, 793, 636, 496, 372, 265, 174, 100, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 100, 174, 265, 372, 496, 636, 793, 966, 1156, 1362, 1585, 1824, 2080, 2352, 2641, 2946, 3268, 3606, 3961] : Array ℕ)[i.val]!

private def up57 (i : Fin (2*57)) : ℕ :=
  (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 512, 0, 991, 0, 1436, 0, 1849, 0, 2228, 0, 2575, 0, 2888, 0, 3169, 0, 3416, 0, 3689, 0, 3961, 0, 4233, 0, 4505, 0, 4786, 0, 5034, 0, 5248, 0, 5430, 0, 5578, 0, 5694, 0, 5776, 0, 5826, 0, 5842, 0, 5826, 0, 5776, 0, 5694, 0, 5578, 0, 5430, 0, 5248, 0, 5034, 0, 4786, 0, 4505, 0, 4233, 0, 3961, 0, 3689, 0, 3416, 0, 3169, 0, 2888, 0, 2575, 0, 2228, 0, 1849, 0, 1436, 0, 991, 0, 512, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Array ℕ)[i.val]!

private def down57 (i : Fin (2*57)) : ℕ :=
  (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 512, 0, 991, 0, 1436, 0, 1849, 0, 2228, 0, 2575, 0, 2888, 0, 3169, 0, 3416, 0, 3689, 0, 3961, 0, 4233, 0, 4505, 0, 4786, 0, 5034, 0, 5248, 0, 5430, 0, 5578, 0, 5694, 0, 5776, 0, 5826, 0, 5842, 0, 5826, 0, 5776, 0, 5694, 0, 5578, 0, 5430, 0, 5248, 0, 5034, 0, 4786, 0, 4505, 0, 4233, 0, 3961, 0, 3689, 0, 3416, 0, 3169, 0, 2888, 0, 2575, 0, 2228, 0, 1849, 0, 1436, 0, 991, 0, 512, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Array ℕ)[i.val]!

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem cover57 : ∀ p : Square 57, (p.1.val+p.2.val)%2=0 →
    10000 ≤ row57 p.1 + col57 p.2 + up57 (sumLine p) + down57 (diffLine p) := by decide +kernel

set_option maxRecDepth 10000 in
private theorem cost57 : (∑ i, row57 i) + (∑ i, col57 i) +
    (∑ i, up57 i) + (∑ i, down57 i) = 449480 := by decide +kernel

set_option maxRecDepth 10000 in
theorem cap57 {s : Finset (Square 57)} (hs : valid s) : s.card ≤ 44 := by
  have h := weighted_cap row57 col57 up57 down57 cover57 hs
  have hh := h.trans_eq cost57
  clear h
  omega

private def placement57 : Finset (Square 57) :=
  ([(0,36), (1,33), (2,18), (3,13), (4,22), (5,9), (6,34), (7,21), (8,50), (9,3), (10,40), (12,10), (13,35), (14,52), (15,15), (16,56), (17,7), (18,0), (19,43), (21,55), (24,8), (27,53), (32,28), (33,45), (34,54), (36,2), (37,5), (38,46), (40,14), (41,11), (42,4), (43,1), (45,51), (46,48), (47,23), (48,20), (49,41), (50,6), (51,31), (52,12), (53,39), (54,32), (55,19), (56,44)] : List (Square 57)).toFinset

set_option maxRecDepth 10000 in
theorem exact57 : IsGreatest {k : ℕ | ∃ s : Finset (Square 57), valid s ∧ s.card=k} 44 := by
  constructor
  · exact ⟨placement57, valid_of_counts placement57 44 (by decide +kernel) (by decide +kernel), by decide +kernel⟩
  · rintro k ⟨s,hs,rfl⟩
    exact cap57 hs

end OMA.BlackQueens


/-! A second-moment bound for nonattacking queens on one color. -/
namespace OMA.QueenMoments
open Finset OMA.S_oeis_a352241

private lemma consecutive (n : ℕ) (z : ℤ) :
    3 * ∑ i ∈ range n, (2*(i:ℤ)-z)^2 =
      (n:ℤ)*((n:ℤ)^2-1) + 3*(n:ℤ)*((n:ℤ)-1-z)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    linear_combination ih

/-- Among two sets of equal size, the one using the cheapest entries has least total weight. -/
private lemma compare_sets {α : Type} [DecidableEq α] (s t : Finset α) (f : α → ℤ) (K : ℤ)
    (hc : s.card = t.card) (hi : ∀ i ∈ s, f i ≤ K) (ho : ∀ i ∉ s, K ≤ f i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ t, f i := by
  let u := s ∩ t
  have us : u ⊆ s := inter_subset_left
  have ut : u ⊆ t := inter_subset_right
  have hcard : (s \ u).card = (t \ u).card := by simp [card_sdiff_of_subset us,card_sdiff_of_subset ut,hc]
  have h1 := sum_le_sum (s := s \ u) (g := fun _ => K) (fun i h => hi i (mem_sdiff.mp h).1)
  have h2 := sum_le_sum (s := t \ u) (f := fun _ => K) (fun i h => ho i (fun his =>
    (mem_sdiff.mp h).2 (mem_inter.mpr ⟨his,(mem_sdiff.mp h).1⟩)))
  rw [sum_const,hcard] at h1
  rw [sum_const] at h2
  have hs := sum_sdiff us (f := f)
  have ht := sum_sdiff ut (f := f)
  omega

/-- The sharp lower bound up to the choice of parity of the centered interval. -/
theorem square_mass (s : Finset ℤ) (z : ℤ) :
    (s.card:ℤ)*((s.card:ℤ)^2-1) ≤ 3*∑ x ∈ s, (2*x-z)^2 := by
  let n := s.card
  let l := (z-(n:ℤ)+1)/2
  let f (i : ℕ) : ℤ := l+i
  let t := (range n).image f
  have fi : Function.Injective f := by intro i j h; dsimp [f] at h; omega
  have ht : t.card=n := by simp [t,card_image_of_injective _ fi]
  have left : -(n:ℤ) ≤ 2*l-z := by dsimp [l]; omega
  have right : 2*l-z ≤ 1-(n:ℤ) := by dsimp [l]; omega
  have hcomp := compare_sets t s (fun x => (2*x-z)^2) ((n:ℤ)^2) ht (by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    have hi' := mem_range.mp hi
    have h1 : -(n:ℤ) ≤ 2*f i-z := by dsimp [f]; omega
    have h2 : 2*f i-z ≤ (n:ℤ) := by dsimp [f]; omega
    nlinarith [mul_nonneg (show 0 ≤ (n:ℤ)+(2*f i-z) by omega) (show 0 ≤ (n:ℤ)-(2*f i-z) by omega)]) (by
    intro x hx
    have outside : x < l ∨ l+(n:ℤ) ≤ x := by
      by_contra! hn
      apply hx
      exact mem_image.mpr ⟨(x-l).toNat,mem_range.mpr (by omega),by dsimp [f]; omega⟩
    rcases outside with h|h
    · have h1 : 2*x-z ≤ -(n:ℤ) := by omega
      nlinarith [mul_nonneg (show 0 ≤ -(2*x-z)-(n:ℤ) by omega) (show 0 ≤ -(2*x-z)+(n:ℤ) by omega)]
    · have h1 : (n:ℤ) ≤ 2*x-z := by omega
      nlinarith [mul_nonneg (show 0 ≤ (2*x-z)-(n:ℤ) by omega) (show 0 ≤ (2*x-z)+(n:ℤ) by omega)])
  have htSum : (∑ x ∈ t, (2*x-z)^2) = ∑ i ∈ range n, (2*(i:ℤ)-(z-2*l))^2 := by
    dsimp only [t]
    rw [sum_image fi.injOn]
    apply sum_congr rfl
    intro i _
    dsimp [f]
    ring
  rw [htSum] at hcomp
  have hbase := consecutive n (z-2*l)
  change (n:ℤ)*((n:ℤ)^2-1) ≤ _
  nlinarith [mul_nonneg (show 0 ≤ (n:ℤ) by positivity) (sq_nonneg ((n:ℤ)-1-(z-2*l)))]


private lemma mass_image {α : Type} (s : Finset α) (f : α → ℤ)
    (hi : Set.InjOn f (s : Set α)) (z : ℤ) :
    (s.card:ℤ)*((s.card:ℤ)^2-1) ≤ 3*∑ p ∈ s, (2*f p-z)^2 := by
  have := square_mass (s.image f) z
  simpa only [card_image_of_injOn hi,sum_image hi] using this

private lemma axis_mass {α : Type} {n : ℕ} (s : Finset α) (f : α → Fin n)
    (hi : Set.InjOn f (s : Set α)) :
    3*(∑ p ∈ s, (2*((f p).val:ℤ)-((n:ℤ)-1))^2) +
      ((n:ℤ)-s.card)*(((n:ℤ)-s.card)^2-1) ≤ (n:ℤ)*((n:ℤ)^2-1) := by
  let t := s.image f
  let miss := (univ : Finset (Fin n)) \ t
  let w (i : Fin n) : ℤ := (2*(i.val:ℤ)-((n:ℤ)-1))^2
  have hcard : t.card = s.card := card_image_of_injOn hi
  have hn : s.card ≤ n := by simpa [hcard] using card_le_card (subset_univ t)
  have hm : (miss.card:ℤ) = (n:ℤ)-s.card := by
    simp [miss,card_sdiff_of_subset (subset_univ t),hcard,Nat.cast_sub hn]
  have mass := mass_image miss (fun i : Fin n => (i.val:ℤ)) (by
    intro a _ b _ h; change (a.val:ℤ) = b.val at h; exact Fin.ext (by exact_mod_cast h)) ((n:ℤ)-1)
  rw [hm] at mass
  have hsplit : (∑ i ∈ miss, w i) + (∑ i ∈ t, w i) = ∑ i, w i := sum_sdiff (subset_univ t)
  have total : 3*(∑ i : Fin n, w i) = (n:ℤ)*((n:ℤ)^2-1) := by
    dsimp only [w]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (2*(i:ℤ)-((n:ℤ)-1))^2) n]
    simpa using consecutive n ((n:ℤ)-1)
  have im : (∑ i ∈ t, w i) = ∑ p ∈ s, w (f p) := sum_image hi
  change _ ≤ 3*(∑ i ∈ miss,w i) at mass
  change 3*(∑ p ∈ s,w (f p)) + _ ≤ _
  linarith only [mass, hsplit, total, im]

/-- A universal inequality for Q nonattacking queens of the same square color. -/
theorem bound {n : ℕ} {s : Finset (Square n)} (hs : valid s) :
    (s.card:ℤ)^2 + 3*(n:ℤ)*s.card ≤ 3*(n:ℤ)^2+1 := by
  let z : ℤ := n-1
  let r (p : Square n) : ℤ := p.1.val
  let c (p : Square n) : ℤ := p.2.val
  let a (p : Square n) := (r p+c p)/2
  let b (p : Square n) := (r p-c p)/2
  obtain ⟨hb,hr,hc,hu,hd⟩ := hs
  have ha (p) (hp : p ∈ s) : 2*a p = r p+c p := by
    have := hb p hp
    dsimp [a,r,c]
    omega
  have hb' (p) (hp : p ∈ s) : 2*b p = r p-c p := by
    have := hb p hp
    dsimp [b,r,c]
    omega
  have ai : Set.InjOn a (s : Set _) := by
    intro p hp q hq he
    apply hu hp hq
    apply Fin.ext
    have h1 := ha p hp
    have h2 := ha q hq
    rw [he] at h1
    simp only [r,c,sumLine] at h1 h2 ⊢
    omega
  have bi : Set.InjOn b (s : Set _) := by
    intro p hp q hq he
    apply hd hp hq
    apply Fin.ext
    have h1 := hb' p hp
    have h2 := hb' q hq
    rw [he] at h1
    have := p.2.isLt
    have := q.2.isLt
    simp only [r,c,diffLine] at h1 h2 ⊢
    omega
  have hrow := axis_mass s Prod.fst hr
  have hcol := axis_mass s Prod.snd hc
  have hA := mass_image s a ai z
  have hB := mass_image s b bi 0
  simp only [sub_zero] at hB
  have identity :
      ∑ p ∈ s, ((2*r p-z)^2+(2*c p-z)^2) =
        ∑ p ∈ s, 2*((2*a p-z)^2+(2*b p)^2) := by
    apply sum_congr rfl
    intro p hp
    rw [ha p hp,hb' p hp]
    ring
  simp only [sum_add_distrib,← mul_sum] at identity
  change 3*(∑ p ∈ s,(2*r p-z)^2) + _ ≤ _ at hrow
  change 3*(∑ p ∈ s,(2*c p-z)^2) + _ ≤ _ at hcol
  by_cases he : s.card = 0
  · rw [he]; push_cast; nlinarith [sq_nonneg (n:ℤ)]
  by_contra! bad
  have pos := mul_pos (show (0:ℤ)<s.card by exact_mod_cast Nat.pos_of_ne_zero he) (sub_pos.mpr bad)
  nlinarith only [hrow,hcol,hA,hB,identity,pos]


private lemma numeric {n : ℕ} (hn : 159 ≤ n) :
    3*(n:ℤ)^2+1 < (proposed n:ℤ)^2+3*(n:ℤ)*proposed n := by
  by_cases he : n=159
  · subst n; decide
  let k := n/5
  have hk : 32 ≤ k := by dsimp [k]; omega
  have hk' : (32:ℤ) ≤ k := by exact_mod_cast hk
  have hdiv : (n:ℤ)/5 = (k:ℤ) := by dsimp [k]
  have hn' : (n:ℤ) = 5*(k:ℤ)+(n%5:ℕ) := by dsimp [k]; omega
  have hm : 0 ≤ (k:ℤ)*((k:ℤ)-32) := mul_nonneg (by positivity) (by omega)
  have hcut : 1 ≤ 4*(n/5) := by omega
  have hcases : n%5=0 ∨ n%5=1 ∨ n%5=2 ∨ n%5=3 ∨ n%5=4 := by omega
  rcases hcases with h|h|h|h|h <;> simp only [proposed,h] <;>
    push_cast [Nat.cast_sub hcut] <;> rw [hdiv,hn',h] <;> push_cast <;> nlinarith only [hm,hk']

/-- The proposed residue-class formula overestimates every order from 159 onward. -/
theorem eventual_failure {n : ℕ} (hn : 159 ≤ n) {s : Finset (Square n)} (hs : valid s) :
    s.card < proposed n := by
  by_contra! he
  have hle : (proposed n:ℤ) ≤ s.card := by exact_mod_cast he
  have hsq : (proposed n:ℤ)^2 ≤ (s.card:ℤ)^2 := by gcongr
  have hmul := mul_le_mul_of_nonneg_left hle (show 0 ≤ 3*(n:ℤ) by positivity)
  linarith only [hmul,hsq,bound hs,numeric hn]

end OMA.QueenMoments

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a352241.main) := by
  intro h
  have hx := (h 52 (by decide)).unique OMA.BlackQueens.exact52
  exact (by decide : OMA.S_oeis_a352241.proposed 52 ≠ 40) hx
