import OMAStatements.S_oeis_a175287
import Mathlib

/-!
# OEIS A175287: a(n) is the number of perimeter-magic triangles of order 3 with magic sum n+2, counted up to rotation

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. (1) A magic triangle is determined by its corners (x0, x1, x2), positive with every pair sum at most
N (the middles are s minus the pair sums); rotation of the triangle is cyclic rotation of the
corners. (2) Sort the corners as x <= y <= z; the constraints reduce to y + z <= N. Three distinct
values give two cyclic classes, otherwise one. (3) For fixed y with 1 <= y <= floor(N/2): z = y
contributes y classes; each of the N - 2y values z > y contributes 2(y-1) + 1 = 2y - 1. So the count
is B(N) = Sum_{y=1..floor(N/2)} (y + (N - 2y)(2y - 1)), which is (4h^3 - 3h^2 + 5h)/6 for N = 2h and
(4h^3 + 3h^2 + 5h)/6 for N = 2h+1. (4) The partial sums of ceiling(j^2/4) have the same closed
forms: a(2h-1) = (4h^3 - 3h^2 + 5h)/6 and a(2h) = (4h^3 + 3h^2 + 5h)/6.
-/

open OMA.S_oeis_a175287

namespace OMA.A175287Proof

/-- A canonical representative starts at a minimum corner. If the minimum
occurs twice, its two occurrences come first and second. -/
abbrev Triple := ℕ × ℕ × ℕ

def Valid (s : ℕ) (p : Triple) : Prop :=
  1 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2 ∧
    (p.2.2 = p.1 → p.2.1 = p.1) ∧ p.2.1 + p.2.2 < s

instance (s : ℕ) : DecidablePred (Valid s) := fun _ => by
  unfold Valid
  infer_instance

def reps (s : ℕ) : Finset Triple :=
  ((Finset.range s).product ((Finset.range s).product (Finset.range s))).filter (Valid s)

@[simp] lemma mem_reps (s : ℕ) (p : Triple) : p ∈ reps s ↔ Valid s p := by
  rcases p with ⟨x, y, z⟩
  simp [reps, Valid]
  omega

def rot {s : ℕ} (t : Fin 6 → Fin (s + 1)) : Fin 6 → Fin (s + 1) :=
  fun i => t (i + 2)

lemma rot_three {s : ℕ} (t : Fin 6 → Fin (s + 1)) : rot (rot (rot t)) = t := by
  funext i
  fin_cases i <;> rfl

lemma orbit_rot {s : ℕ} (t : Fin 6 → Fin (s + 1)) : orbit (rot t) = orbit t := by
  have h : (fun i => t (i + 4)) = rot (rot t) := by
    funext i
    fin_cases i <;> rfl
  have hh : (fun i => rot t (i + 4)) = t := by
    funext i
    fin_cases i <;> rfl
  simp only [orbit, h, hh]
  change {rot t, rot (rot t), t} = {t, rot t, rot (rot t)}
  ext u
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma orbit_eq_iff {s : ℕ} (t u : Fin 6 → Fin (s + 1)) :
    orbit t = orbit u ↔ t = u ∨ t = rot u ∨ t = rot (rot u) := by
  constructor
  · intro h
    have ht : t ∈ orbit u := h ▸ (by simp [orbit])
    have hh : (fun i => u (i + 4)) = rot (rot u) := by
      funext i
      fin_cases i <;> rfl
    simp only [orbit, Finset.mem_insert, Finset.mem_singleton, hh] at ht
    exact ht
  · rintro (rfl | rfl | rfl)
    · rfl
    · exact orbit_rot u
    · rw [orbit_rot, orbit_rot]

lemma magic_rot {s : ℕ} {t : Fin 6 → Fin (s + 1)} (ht : Magic s t) :
    Magic s (rot t) := by
  rcases ht with ⟨hp, h0, h2, h4⟩
  refine ⟨fun i => hp (i + 2), ?_, ?_, ?_⟩
  · exact h2
  · exact h4
  · exact h0

def corners {s : ℕ} (t : Fin 6 → Fin (s + 1)) : Triple :=
  ((t 0).val, (t 2).val, (t 4).val)

def Canonical {s : ℕ} (t : Fin 6 → Fin (s + 1)) : Prop :=
  (t 0).val ≤ (t 2).val ∧ (t 0).val ≤ (t 4).val ∧
    ((t 4).val = (t 0).val → (t 2).val = (t 0).val)

lemma canonical_exists {s : ℕ} (t : Fin 6 → Fin (s + 1)) :
    Canonical t ∨ Canonical (rot t) ∨ Canonical (rot (rot t)) := by
  simp only [Canonical, rot]
  change ((t 0).val ≤ (t 2).val ∧ (t 0).val ≤ (t 4).val ∧
      ((t 4).val = (t 0).val → (t 2).val = (t 0).val)) ∨
    ((t 2).val ≤ (t 4).val ∧ (t 2).val ≤ (t 0).val ∧
      ((t 0).val = (t 2).val → (t 4).val = (t 2).val)) ∨
    ((t 4).val ≤ (t 0).val ∧ (t 4).val ≤ (t 2).val ∧
      ((t 2).val = (t 4).val → (t 0).val = (t 4).val))
  omega

lemma valid_corners {s : ℕ} {t : Fin 6 → Fin (s + 1)}
    (hm : Magic s t) (hc : Canonical t) : Valid s (corners t) := by
  have h1 := hm.1 0
  have h3 := hm.1 3
  rcases hm with ⟨hp, h0, h2, h4⟩
  rcases hc with ⟨hc1, hc2, hc3⟩
  dsimp [Valid, corners]
  omega

lemma magic_ext {s : ℕ} {t u : Fin 6 → Fin (s + 1)}
    (ht : Magic s t) (hu : Magic s u) (hc : corners t = corners u) : t = u := by
  have h0 := congrArg (fun p : Triple => p.1) hc
  have h2 := congrArg (fun p : Triple => p.2.1) hc
  have h4 := congrArg (fun p : Triple => p.2.2) hc
  dsimp [corners] at h0 h2 h4
  rcases ht with ⟨_, ht0, ht2, ht4⟩
  rcases hu with ⟨_, hu0, hu2, hu4⟩
  funext i
  apply Fin.ext
  fin_cases i
  · exact h0
  · change (t 1).val = (u 1).val
    omega
  · exact h2
  · change (t 3).val = (u 3).val
    omega
  · exact h4
  · change (t 5).val = (u 5).val
    omega

lemma canonical_unique {s : ℕ} {t u : Fin 6 → Fin (s + 1)}
    (ht : Canonical t) (hu : Canonical u) (he : orbit t = orbit u) :
    corners t = corners u := by
  rcases (orbit_eq_iff t u).mp he with h | h | h
  · exact congrArg corners h
  · subst t
    rcases ht with ⟨ht1, ht2, ht3⟩
    rcases hu with ⟨hu1, hu2, hu3⟩
    change (u 2).val ≤ (u 4).val at ht1
    change (u 2).val ≤ (u 0).val at ht2
    change ((u 0).val = (u 2).val → (u 4).val = (u 2).val) at ht3
    apply Prod.ext
    · change (u 2).val = (u 0).val
      omega
    · apply Prod.ext
      · change (u 4).val = (u 2).val
        omega
      · change (u 0).val = (u 4).val
        omega
  · subst t
    rcases ht with ⟨ht1, ht2, ht3⟩
    rcases hu with ⟨hu1, hu2, hu3⟩
    change (u 4).val ≤ (u 0).val at ht1
    change (u 4).val ≤ (u 2).val at ht2
    change ((u 2).val = (u 4).val → (u 0).val = (u 4).val) at ht3
    apply Prod.ext
    · change (u 4).val = (u 0).val
      omega
    · apply Prod.ext
      · change (u 0).val = (u 2).val
        omega
      · change (u 2).val = (u 4).val
        omega

def bounded (s v : ℕ) : Fin (s + 1) :=
  ⟨min v s, Nat.lt_succ_of_le (Nat.min_le_right v s)⟩

lemma bounded_val {s v : ℕ} (h : v ≤ s) : (bounded s v).val = v :=
  Nat.min_eq_left h

def triangle (s : ℕ) (p : Triple) : Fin 6 → Fin (s + 1) :=
  ![bounded s p.1, bounded s (s - p.1 - p.2.1), bounded s p.2.1,
    bounded s (s - p.2.1 - p.2.2), bounded s p.2.2,
    bounded s (s - p.2.2 - p.1)]

lemma triangle_values {s : ℕ} {p : Triple} (h : Valid s p) :
    (fun i => (triangle s p i).val) =
      ![p.1, s - p.1 - p.2.1, p.2.1, s - p.2.1 - p.2.2,
        p.2.2, s - p.2.2 - p.1] := by
  rcases p with ⟨x, y, z⟩
  dsimp [Valid] at h
  funext i
  fin_cases i <;> simp [triangle, bounded, show x ≤ s by omega,
    show y ≤ s by omega, show z ≤ s by omega] <;> omega

lemma triangle_spec {s : ℕ} {p : Triple} (h : Valid s p) :
    Magic s (triangle s p) ∧ Canonical (triangle s p) ∧ corners (triangle s p) = p := by
  have hv := triangle_values h
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  have h3 := congrFun hv 3
  have h4 := congrFun hv 4
  have h5 := congrFun hv 5
  simp at h0 h1 h2 h3 h4 h5
  rcases p with ⟨x, y, z⟩
  dsimp only at h0 h1 h2 h3 h4 h5
  dsimp [Valid] at h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i
    have hi := congrFun hv i
    rw [hi]
    fin_cases i <;> simp <;> omega
  · omega
  · omega
  · omega
  · dsimp only [Canonical]
    omega
  · simp [corners, h0, h2, h4]

lemma triangles_eq_card (s : ℕ) : triangles s = (reps s).card := by
  classical
  symm
  apply Finset.card_bij (fun p _ => orbit (triangle s p))
  · intro p hp
    have hm := (triangle_spec ((mem_reps s p).mp hp)).1
    exact Finset.mem_image.mpr ⟨triangle s p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, rfl⟩
  · intro p hp q hq he
    obtain ⟨_, hpc, hpe⟩ := triangle_spec ((mem_reps s p).mp hp)
    obtain ⟨_, hqc, hqe⟩ := triangle_spec ((mem_reps s q).mp hq)
    have hh := canonical_unique hpc hqc he
    simpa only [hpe, hqe] using hh
  · intro o ho
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ho
    have hm := (Finset.mem_filter.mp ht).2
    have lift : ∀ u, Magic s u → Canonical u → orbit u = orbit t →
        ∃ p, ∃ hp : p ∈ reps s, orbit (triangle s p) = orbit t := by
      intro u hu hc he
      have hv := valid_corners hu hc
      refine ⟨corners u, (mem_reps _ _).mpr hv, ?_⟩
      have hs := triangle_spec hv
      rw [magic_ext hs.1 hu hs.2.2]
      exact he
    rcases canonical_exists t with hc | hc | hc
    · exact lift t hm hc rfl
    · exact lift (rot t) (magic_rot hm) hc (orbit_rot t)
    · exact lift (rot (rot t)) (magic_rot (magic_rot hm)) hc
        ((orbit_rot (rot t)).trans (orbit_rot t))


def staircase (k : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range k).sigma (fun i => Finset.range (i + 1))

def boundary (k : ℕ) : Finset Triple :=
  (staircase k).image (fun p => (1, p.2 + 1, p.1 - p.2 + 2))

lemma boundary_card (k : ℕ) :
    (boundary k).card = ∑ i ∈ Finset.range k, (i + 1) := by
  rw [boundary, Finset.card_image_of_injOn]
  · simp [staircase, Finset.card_sigma]
  · intro p hp q hq he
    have hp' := hp
    have hq' := hq
    simp [staircase] at hp' hq'
    have h1 := congrArg (fun t : Triple => t.2.1) he
    have h2 := congrArg (fun t : Triple => t.2.2) he
    dsimp at h1 h2
    have hfirst : p.1 = q.1 := by omega
    have hsecond : p.2 = q.2 := by omega
    rcases p with ⟨i, j⟩
    rcases q with ⟨a, b⟩
    dsimp at hfirst hsecond
    subst a
    subst b
    rfl

lemma boundary_not_constant (k : ℕ) : (1, 1, 1) ∉ boundary k := by
  simp only [boundary, Finset.mem_image]
  rintro ⟨p, _, he⟩
  have hh := congrArg (fun t : Triple => t.2.2) he
  dsimp at hh
  omega

lemma boundary_eq (k : ℕ) :
    (reps (k + 3)).filter (fun p => p.1 = 1) =
      insert (1, 1, 1) (boundary k) := by
  ext p
  rcases p with ⟨x, y, z⟩
  simp only [Finset.mem_filter, mem_reps, Finset.mem_insert]
  constructor
  · rintro ⟨hv, hx⟩
    dsimp [Valid] at hv
    by_cases hz : z = 1
    · left
      apply Prod.ext
      · exact hx
      · apply Prod.ext <;> dsimp <;> omega
    · right
      apply Finset.mem_image.mpr
      refine ⟨⟨y + z - 3, y - 1⟩, ?_, ?_⟩
      · simp only [staircase, Finset.mem_sigma, Finset.mem_range]
        omega
      · apply Prod.ext
        · exact hx.symm
        · apply Prod.ext <;> dsimp <;> omega
  · rintro (he | he)
    · cases he
      simp [Valid]
    · obtain ⟨p, hp, he⟩ := Finset.mem_image.mp he
      simp only [staircase, Finset.mem_sigma, Finset.mem_range] at hp
      have h1 := congrArg (fun t : Triple => t.1) he
      have h2 := congrArg (fun t : Triple => t.2.1) he
      have h3 := congrArg (fun t : Triple => t.2.2) he
      dsimp at h1 h2 h3
      dsimp [Valid]
      omega

lemma interior_card (s : ℕ) :
    ((reps (s + 2)).filter (fun p => p.1 ≠ 1)).card = (reps s).card := by
  symm
  apply Finset.card_bij (fun p _ => (p.1 + 1, p.2.1 + 1, p.2.2 + 1))
  · intro p hp
    have hv := (mem_reps _ _).mp hp
    simp only [Finset.mem_filter, mem_reps]
    dsimp [Valid] at hv ⊢
    omega
  · intro p hp q hq he
    have h1 := congrArg (fun t : Triple => t.1) he
    have h2 := congrArg (fun t : Triple => t.2.1) he
    have h3 := congrArg (fun t : Triple => t.2.2) he
    apply Prod.ext
    · dsimp at h1
      omega
    · apply Prod.ext
      · dsimp at h2
        omega
      · dsimp at h3
        omega
  · intro p hp
    simp only [Finset.mem_filter, mem_reps] at hp
    dsimp [Valid] at hp
    refine ⟨(p.1 - 1, p.2.1 - 1, p.2.2 - 1), ?_, ?_⟩
    · rw [mem_reps]
      dsimp [Valid]
      omega
    · apply Prod.ext
      · dsimp
        omega
      · apply Prod.ext <;> dsimp <;> omega

lemma reps_step (k : ℕ) :
    (reps (k + 3)).card = (reps (k + 1)).card +
      (∑ i ∈ Finset.range k, (i + 1)) + 1 := by
  have h := (reps (k + 3)).card_filter_add_card_filter_not (fun p => p.1 = 1)
  rw [boundary_eq, Finset.card_insert_of_notMem (boundary_not_constant k), boundary_card] at h
  have hi := interior_card (k + 1)
  have he : k + 1 + 2 = k + 3 := by omega
  rw [he] at hi
  rw [hi] at h
  omega

lemma reps_two : (reps 2).card = 0 := by
  have he : reps 2 = ∅ := by
    ext p
    simp only [mem_reps, Finset.notMem_empty, iff_false]
    dsimp [Valid]
    omega
  rw [he]
  rfl

lemma reps_three : (reps 3).card = 1 := by
  have he : reps 3 = {(1, 1, 1)} := by
    ext p
    rcases p with ⟨x, y, z⟩
    simp only [mem_reps, Finset.mem_singleton, Prod.mk.injEq]
    dsimp [Valid]
    omega
  rw [he]
  rfl

lemma sum_twice (k : ℕ) :
    2 * (∑ i ∈ Finset.range k, (i + 1)) = k * (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    nlinarith

lemma square_pair (n : ℕ) :
    2 * (((n + 1) ^ 2 + 3) / 4 + ((n + 2) ^ 2 + 3) / 4) =
      (n + 1) * (n + 2) + 2 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst n
    ring_nf
    omega
  · subst n
    ring_nf
    omega

lemma a_step (n : ℕ) : a (n + 2) = a n +
    (∑ i ∈ Finset.range (n + 1), (i + 1)) + 1 := by
  have hs := sum_twice (n + 1)
  have hp := square_pair n
  unfold a
  rw [show n + 2 + 1 = (n + 1) + 1 + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.add_assoc] at hs ⊢
  nlinarith [hp, hs]

lemma count_all (n : ℕ) : a n = (reps (n + 2)).card := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [a] using reps_two.symm
  | one => simpa [a, Finset.sum_range_succ] using reps_three.symm
  | more n hn hn1 =>
    rw [a_step, hn]
    have h := reps_step (n + 1)
    convert h.symm using 1

end OMA.A175287Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a175287.main := by
  intro n
  rw [OMA.A175287Proof.triangles_eq_card]
  exact OMA.A175287Proof.count_all n

