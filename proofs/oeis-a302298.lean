import OMAStatements.S_oeis_a302298
import Mathlib

namespace OMA.S_oeis_a302298
open Finset

lemma rowsum (w : ℕ → ℤ) (N : ℕ) :
    ∑ i ∈ range N, w i * ((N : ℤ) - i) = ∑ k ∈ range N, ∑ i ∈ range (k + 1), w i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ (fun k => ∑ i ∈ range (k + 1), w i), ← ih]
    have h : ∑ i ∈ range (N + 1), w i * (((N + 1 : ℕ) : ℤ) - i)
        = ∑ i ∈ range (N + 1), (w i * ((N : ℤ) - i) + w i) := by
      apply sum_congr rfl; intro i _; push_cast; ring
    rw [h, sum_add_distrib, sum_range_succ (fun i => w i * ((N : ℤ) - i))]
    simp

lemma cut (w : ℕ → ℤ) (N : ℕ) :
    ∑ i ∈ range N, ∑ j ∈ range N, w i * w j * |(i : ℤ) - j|
      = 2 * ∑ k ∈ range N, (∑ i ∈ range (k + 1), w i) *
          (∑ i ∈ range N, w i - ∑ i ∈ range (k + 1), w i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hr := rowsum w N
    rw [sum_range_succ, sum_range_succ (fun k => (∑ i ∈ range (k + 1), w i) *
          (∑ i ∈ range (N + 1), w i - ∑ i ∈ range (k + 1), w i))]
    have e1 : ∀ i ∈ range N, ∑ j ∈ range (N + 1), w i * w j * |(i : ℤ) - j|
        = ∑ j ∈ range N, w i * w j * |(i : ℤ) - j| + w i * w N * ((N : ℤ) - i) := by
      intro i hi
      rw [sum_range_succ]
      have : (i : ℤ) < N := by exact_mod_cast mem_range.mp hi
      rw [abs_sub_comm, abs_of_pos (by linarith)]
    rw [sum_congr rfl e1, sum_add_distrib]
    have e2 : ∑ j ∈ range (N + 1), w N * w j * |((N : ℕ) : ℤ) - j|
        = ∑ j ∈ range N, w N * w j * ((N : ℤ) - j) := by
      rw [sum_range_succ]
      simp only [sub_self, abs_zero, mul_zero, add_zero]
      apply sum_congr rfl; intro j hj
      have : (j : ℤ) < N := by exact_mod_cast mem_range.mp hj
      rw [abs_of_pos (by linarith)]
    rw [e2]
    have e3 : ∑ i ∈ range N, w i * w N * ((N : ℤ) - i) = w N * ∑ i ∈ range N, w i * ((N : ℤ) - i) := by
      rw [mul_sum]; apply sum_congr rfl; intro i _; ring
    have e4 : ∑ j ∈ range N, w N * w j * ((N : ℤ) - j) = w N * ∑ i ∈ range N, w i * ((N : ℤ) - i) := by
      rw [mul_sum]; apply sum_congr rfl; intro i _; ring
    rw [e3, e4, hr, ih]
    have e5 : ∀ k ∈ range N, (∑ i ∈ range (k + 1), w i) *
          (∑ i ∈ range (N + 1), w i - ∑ i ∈ range (k + 1), w i)
        = (∑ i ∈ range (k + 1), w i) * (∑ i ∈ range N, w i - ∑ i ∈ range (k + 1), w i)
          + w N * ∑ i ∈ range (k + 1), w i := by
      intro k _; rw [sum_range_succ _ N]; ring
    rw [sum_congr rfl e5, sum_add_distrib, ← mul_sum]
    have : ∑ i ∈ range (N + 1), w i - ∑ i ∈ range (N + 1), w i = 0 := sub_self _
    rw [this]
    ring

/-- tent weights -/
def w (n : ℕ) (i : ℕ) : ℤ := 2 * n + 1 - 2 * |(i : ℤ) - n|

lemma P1 (n : ℕ) : ∀ k, k ≤ n + 1 → ∑ i ∈ range k, w n i = (k : ℤ) ^ 2 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [sum_range_succ, ih (by omega)]
    have : |(k : ℤ) - n| = (n : ℤ) - k := by
      rw [abs_sub_comm, abs_of_nonneg (by omega)]
    simp only [w, this]
    push_cast; ring

lemma P2 (n : ℕ) : ∀ j, j ≤ n →
    ∑ i ∈ range (n + 1 + j), w n i = 2 * (n : ℤ) ^ 2 + 2 * n + 1 - ((n : ℤ) - j) ^ 2 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [add_zero, P1 n (n + 1) le_rfl]; push_cast; ring
  | succ j ih =>
    intro hj
    rw [← add_assoc, sum_range_succ, ih (by omega)]
    have : |((n + 1 + j : ℕ) : ℤ) - n| = (j : ℤ) + 1 := by
      push_cast; rw [abs_of_nonneg (by omega)]; ring
    simp only [w, this]
    push_cast; ring

lemma Qsum (M : ℤ) (N : ℕ) :
    30 * ∑ u ∈ range N, ((u : ℤ) ^ 2 * (M - (u : ℤ) ^ 2))
      = 5 * M * (((N : ℤ) - 1) * N * (2 * N - 1))
        - ((N : ℤ) - 1) * N * (2 * N - 1) * (3 * (N : ℤ) ^ 2 - 3 * N - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih]; push_cast; ring

lemma Hclosed (n : ℕ) :
    (15 : ℤ) * ∑ k ∈ range (2 * n + 1), ((∑ i ∈ range (k + 1), w n i) *
        (2 * (n : ℤ) ^ 2 + 2 * n + 1 - ∑ i ∈ range (k + 1), w n i))
      = (n : ℤ) * (6 + 25 * n + 40 * n ^ 2 + 35 * n ^ 3 + 14 * n ^ 4) := by
  set M : ℤ := 2 * (n : ℤ) ^ 2 + 2 * n + 1 with hM
  set F : ℕ → ℤ := fun u => (u : ℤ) ^ 2 * (M - (u : ℤ) ^ 2) with hF
  rw [show 2 * n + 1 = (n + 1) + n by ring, sum_range_add]
  have e1 : ∀ k ∈ range (n + 1), (∑ i ∈ range (k + 1), w n i) *
        (M - ∑ i ∈ range (k + 1), w n i) = F (k + 1) := by
    intro k hk
    rw [P1 n (k + 1) (by have := mem_range.mp hk; omega)]

  have e2 : ∀ x ∈ range n, (∑ i ∈ range (n + 1 + x + 1), w n i) *
        (M - ∑ i ∈ range (n + 1 + x + 1), w n i) = F (n - 1 - x) := by
    intro x hx
    have hx' := mem_range.mp hx
    have hc : ((n - 1 - x : ℕ) : ℤ) = (n : ℤ) - (x + 1) := by omega
    rw [show n + 1 + x + 1 = n + 1 + (x + 1) by ring, P2 n (x + 1) (by omega)]
    simp only [hF]; rw [hc]; push_cast; rw [← hM]; ring
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_range_reflect F n]
  have h1 := sum_range_succ' F (n + 1)
  have h0 : F 0 = 0 := by simp [hF]
  rw [h0, add_zero] at h1
  rw [← h1]
  have Q1 : 30 * ∑ u ∈ range (n + 1 + 1), F u = _ := Qsum M (n + 1 + 1)
  have Q2 : 30 * ∑ u ∈ range n, F u = _ := Qsum M n
  have key : 30 * (∑ u ∈ range (n + 1 + 1), F u + ∑ u ∈ range n, F u)
      = 2 * ((n : ℤ) * (6 + 25 * n + 40 * n ^ 2 + 35 * n ^ 3 + 14 * n ^ 4)) := by
    rw [mul_add, Q1, Q2, hM]; push_cast; ring
  linarith

lemma htot (n : ℕ) : ∑ i ∈ range (2 * n + 1), w n i = 2 * (n : ℤ) ^ 2 + 2 * n + 1 := by
  have h := P2 n n le_rfl
  rw [show n + 1 + n = 2 * n + 1 by ring] at h
  rw [h]; ring

lemma conv (n : ℕ) (g : ℤ → ℤ) :
    ∑ a ∈ Icc (-(n : ℤ)) n, g a = ∑ i ∈ range (2 * n + 1), g ((i : ℤ) - n) := by
  symm
  apply sum_nbij' (fun i : ℕ => (i : ℤ) - n) (fun a : ℤ => (a + n).toNat)
  · intro i hi; simp only [mem_range, mem_Icc] at *; omega
  · intro a ha; simp only [mem_range, mem_Icc] at *; omega
  · intro i hi; simp only [mem_range] at hi; omega
  · intro a ha; simp only [mem_Icc] at ha; omega
  · intro i hi; rfl

lemma fibcard (n : ℕ) (a : ℤ) (ha : a ∈ Icc (-(n : ℤ)) n) :
    (((diamond n).filter (fun p => p.1 = a)).card : ℤ) = 2 * n + 1 - 2 * |a| := by
  have hab : |a| ≤ (n : ℤ) := by
    rw [abs_le]; simpa [mem_Icc] using ha
  have h : (diamond n).filter (fun p => p.1 = a)
      = (Icc (-((n : ℤ) - |a|)) ((n : ℤ) - |a|)).image (fun c => (a, c)) := by
    ext ⟨x, y⟩
    simp only [diamond, mem_filter, mem_product, mem_Icc, mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩, h6⟩
      refine ⟨y, ⟨?_, ?_⟩, h6.symm, rfl⟩
      · rcases abs_cases a with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases abs_cases y with ⟨hy, _⟩ | ⟨hy, _⟩ <;>
          subst h6 <;> omega
      · rcases abs_cases a with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases abs_cases y with ⟨hy, _⟩ | ⟨hy, _⟩ <;>
          subst h6 <;> omega
    · rintro ⟨c, ⟨h1, h2⟩, h3, rfl⟩
      subst h3
      rcases abs_cases a with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases abs_cases c with ⟨hc', _⟩ | ⟨hc', _⟩ <;>
        refine ⟨⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩, rfl⟩ <;> omega
  rw [h, card_image_of_injective _ (fun x y hxy => (Prod.mk.inj hxy).2), Int.card_Icc]
  have : (0 : ℤ) ≤ (n : ℤ) - |a| := by linarith
  rw [Int.toNat_of_nonneg (by linarith)]
  ring

lemma fib (n : ℕ) (g : ℤ → ℤ) :
    ∑ p ∈ diamond n, g p.1 = ∑ a ∈ Icc (-(n : ℤ)) n, (2 * n + 1 - 2 * |a|) * g a := by
  have hmaps : ∀ p ∈ diamond n, p.1 ∈ Icc (-(n : ℤ)) n := by
    intro p hp
    simp only [diamond, mem_filter, mem_product, mem_Icc] at hp ⊢
    exact hp.1.1
  rw [← sum_fiberwise_of_maps_to (g := Prod.fst) hmaps]
  apply sum_congr rfl
  intro a ha
  have h1 : ∀ p ∈ (diamond n).filter (fun p => p.1 = a), g p.1 = g a := by
    intro p hp; rw [(mem_filter.mp hp).2]
  rw [sum_congr rfl h1, sum_const, nsmul_eq_mul, fibcard n a ha]

lemma Tx (n : ℕ) :
    ∑ p ∈ diamond n, ∑ q ∈ diamond n, |p.1 - q.1|
      = ∑ i ∈ range (2 * n + 1), ∑ j ∈ range (2 * n + 1), w n i * w n j * |(i : ℤ) - j| := by
  have h1 : ∀ p ∈ diamond n, ∑ q ∈ diamond n, |p.1 - q.1|
      = ∑ j ∈ range (2 * n + 1), w n j * |p.1 - ((j : ℤ) - n)| := by
    intro p _
    rw [fib n (fun b => |p.1 - b|), conv n]
    rfl
  rw [sum_congr rfl h1]
  rw [fib n (fun a => ∑ j ∈ range (2 * n + 1), w n j * |a - ((j : ℤ) - n)|), conv n]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  have : |((i : ℤ) - n) - ((j : ℤ) - n)| = |(i : ℤ) - j| := by congr 1; ring
  rw [this]
  simp only [w]; ring

lemma swapsum (n : ℕ) :
    ∑ p ∈ diamond n, ∑ q ∈ diamond n, manhattan p q
      = 2 * ∑ p ∈ diamond n, ∑ q ∈ diamond n, |p.1 - q.1| := by
  have hsw : ∀ g : ℤ × ℤ → ℤ, ∑ p ∈ diamond n, g p = ∑ p ∈ diamond n, g p.swap := by
    intro g
    apply sum_equiv (Equiv.prodComm ℤ ℤ)
    · intro p; simp [diamond, add_comm, and_comm]
    · intro p _; simp
  simp only [manhattan]
  simp only [sum_add_distrib]
  have h2 : ∑ p ∈ diamond n, ∑ q ∈ diamond n, |p.2 - q.2|
      = ∑ p ∈ diamond n, ∑ q ∈ diamond n, |p.1 - q.1| := by
    rw [hsw (fun p => ∑ q ∈ diamond n, |p.2 - q.2|)]
    apply sum_congr rfl
    intro p _
    simp only [Prod.snd_swap]
    rw [hsw (fun q => |p.1 - q.1|)]
    apply sum_congr rfl
    intro q _
    simp
  rw [h2]; ring

theorem main_proof : ∀ n : ℕ,
    a n = 2 * ((n : ℤ) * (6 + 25 * n + 40 * n ^ 2 + 35 * n ^ 3 + 14 * n ^ 4)) / 15 := by
  intro n
  unfold a
  rw [swapsum, Tx, cut, htot]
  have hH := Hclosed n
  generalize (∑ k ∈ range (2 * n + 1), ((∑ i ∈ range (k + 1), w n i) *
        (2 * (n : ℤ) ^ 2 + 2 * n + 1 - ∑ i ∈ range (k + 1), w n i))) = H at hH ⊢
  have h2 : 2 * ((n : ℤ) * (6 + 25 * n + 40 * n ^ 2 + 35 * n ^ 3 + 14 * n ^ 4)) = 15 * (2 * H) := by
    linarith
  rw [h2]
  omega

end OMA.S_oeis_a302298

theorem OMA.solution : type_of% @OMA.S_oeis_a302298.main := by
  exact OMA.S_oeis_a302298.main_proof
