import OMAStatements.S_oeis_a309221
import Mathlib

/-!
# A309221: the normalized expected range of a knight's random walk is an integer

For `n ≥ 1`, `a n` is the total number of visited squares over all `8^n` move sequences, divided by
`8`. The eight symmetries of the square act simply transitively on the eight knight moves: `L m`
sends the move `(false, false, false)` to `m` and permutes the moves via `σ m`. Applying `L m` to a
whole walk maps its visited set injectively, so the size is unchanged (`card_map`). Hence all eight
fibres `{w | w 0 = m}` have the same total (`fiber`), and the sum is `8` times an integer.
-/

namespace OMA.A309221Proof
open OMA.S_oeis_a309221

/-- The symmetry of the square that sends the move `(false, false, false)` to `m`
(swap the coordinates if `m.1`, then negate x if `m.2.1` and y if `m.2.2`). -/
def L (m : Move) (p : ℤ × ℤ) : ℤ × ℤ :=
  let q := if m.1 then (p.2, p.1) else p
  (if m.2.1 then -q.1 else q.1, if m.2.2 then -q.2 else q.2)

/-- The induced permutation of the eight knight moves. -/
def σ (m m' : Move) : Move :=
  (xor m'.1 m.1, xor (if m.1 then m'.2.2 else m'.2.1) m.2.1,
    xor (if m.1 then m'.2.1 else m'.2.2) m.2.2)

lemma jump_σ : ∀ m m' : Move, jump (σ m m') = L m (jump m') := by decide

lemma σ_bij : ∀ m : Move, Function.Bijective (σ m) := by decide

lemma σ_zero : ∀ m : Move, σ m (false, false, false) = m := by decide

lemma L_add (m : Move) (p q : ℤ × ℤ) : L m (p + q) = L m p + L m q := by
  obtain ⟨a, b, c⟩ := m
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  cases a <;> cases b <;> cases c <;> simp [L] <;> ring_nf <;> simp

lemma L_zero (m : Move) : L m 0 = 0 := by
  obtain ⟨a, b, c⟩ := m
  cases a <;> cases b <;> cases c <;> rfl

lemma L_inj (m : Move) : Function.Injective (L m) := by
  intro p q h
  obtain ⟨a, b, c⟩ := m
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  cases a <;> cases b <;> cases c <;> simp [L, Prod.ext_iff] at h ⊢ <;> omega

lemma visited_map (m : Move) : ∀ ws : List Move,
    visited (ws.map (σ m)) = (visited ws).image (L m)
  | [] => by simp [visited, L_zero]
  | m' :: ws => by
    simp only [List.map_cons, visited, visited_map m ws, Finset.image_insert, L_zero,
      Finset.image_image]
    congr 2
    funext p
    simp [jump_σ, L_add]

lemma card_map (m : Move) {n : ℕ} (w : Fin n → Move) :
    (visited (List.ofFn (σ m ∘ w))).card = (visited (List.ofFn w)).card := by
  rw [← List.map_ofFn, visited_map, Finset.card_image_of_injective _ (L_inj m)]

/-- Every fibre `{w | w 0 = m}` has the same total as the fibre of `(false, false, false)`. -/
lemma fiber (n : ℕ) (m : Move) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin (n + 1) → Move => w 0 = m), (visited (List.ofFn w)).card =
    ∑ w ∈ Finset.univ.filter (fun w : Fin (n + 1) → Move => w 0 = (false, false, false)),
      (visited (List.ofFn w)).card := by
  let e : Move ≃ Move := Equiv.ofBijective (σ m) (σ_bij m)
  have he0 : e.symm m = (false, false, false) := by
    rw [Equiv.symm_apply_eq]; exact (σ_zero m).symm
  refine Finset.sum_nbij' (fun w => e.symm ∘ w) (fun w => e ∘ w) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    simp [hw, he0]
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    simp only [Function.comp_apply, hw]
    exact σ_zero m
  · intro w _; funext i; simp
  · intro w _; funext i; simp
  · intro w _
    have := card_map m (e.symm ∘ w)
    have hc : σ m ∘ (e.symm ∘ w) = w := by
      funext i
      show e (e.symm (w i)) = w i
      simp
    rw [hc] at this
    exact this

lemma total (n : ℕ) :
    ∑ w : Fin (n + 1) → Move, (visited (List.ofFn w)).card =
    8 * ∑ w ∈ Finset.univ.filter (fun w : Fin (n + 1) → Move => w 0 = (false, false, false)),
      (visited (List.ofFn w)).card := by
  rw [← Finset.sum_fiberwise Finset.univ (fun w : Fin (n + 1) → Move => w 0)]
  rw [Finset.sum_congr rfl fun m _ => fiber n m, Finset.sum_const, Finset.card_univ]
  rfl

theorem main' : ∀ n : ℕ, ∃ z : ℤ, a n = (z : ℚ) := by
  intro n
  cases n with
  | zero => exact ⟨1, by simp [a]⟩
  | succ n =>
    refine ⟨(∑ w ∈ Finset.univ.filter (fun w : Fin (n + 1) → Move => w 0 = (false, false, false)),
      (visited (List.ofFn w)).card : ℕ), ?_⟩
    simp only [a, expectedRange]
    rw [total, show 3 * (n + 1) - 3 = 3 * n by omega]
    push_cast
    rw [pow_mul, pow_succ]
    norm_num
    field_simp
    ring

end OMA.A309221Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a309221.main := OMA.A309221Proof.main'
