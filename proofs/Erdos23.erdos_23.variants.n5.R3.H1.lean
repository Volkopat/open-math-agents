import OMAReductions.R_Erdos23_erdos_23_variants_n5_R3

/-! A finite interval certificate for the five-colour-class reduction of Erdős problem 23. -/
-- Credit: @STARDUSTLC666

namespace FiveCycleBound

abbrev Row := Fin 5 → ℕ

def allThrough (p : ℕ → Bool) : ℕ → Bool
  | 0 => p 0
  | n + 1 => p (n + 1) && allThrough p n

lemma get {p : ℕ → Bool} {n x : ℕ} (h : allThrough p n = true) (hx : x ≤ n) :
    p x = true := by
  induction n with
  | zero => simpa [allThrough, Nat.eq_zero_of_le_zero hx] using h
  | succ n ih =>
    obtain ⟨top, rest⟩ := Bool.and_eq_true_iff.mp h
    rcases Nat.eq_or_lt_of_le hx with eq | lt
    · simpa [eq] using top
    · exact ih rest (by omega)

def edge (a lo hi : Row) (i j k m n : Fin 5) : Bool :=
  decide (a i * a j + min (hi i + hi j + hi m) (hi k + hi n) ≤ 25 + lo i * lo j)

def box (a lo hi : Row) : Bool :=
  edge a lo hi 0 1 2 3 4 || edge a lo hi 1 2 3 4 0 ||
  edge a lo hi 2 3 4 0 1 || edge a lo hi 3 4 0 1 2 || edge a lo hi 4 0 1 2 3

def Good (a t : Row) : Prop :=
  ∃ i, a i * a (i+1) + min (t i + t (i+1) + t (i+3)) (t (i+2) + t (i+4)) ≤
    25 + t i * t (i+1)

lemma edge_sound {a lo hi t : Row} {i j k m n : Fin 5}
    (h : edge a lo hi i j k m n = true) (lower : lo ≤ t) (upper : t ≤ hi) :
    a i * a j + min (t i + t j + t m) (t k + t n) ≤ 25 + t i * t j := by
  have he := of_decide_eq_true h
  exact (Nat.add_le_add_left (min_le_min
    (Nat.add_le_add (Nat.add_le_add (upper i) (upper j)) (upper m))
    (Nat.add_le_add (upper k) (upper n))) _).trans
    (he.trans (Nat.add_le_add_left (Nat.mul_le_mul (lower i) (lower j)) _))

lemma box_sound {a lo hi t : Row} (h : box a lo hi = true) (lower : lo ≤ t)
    (upper : t ≤ hi) : Good a t := by
  simp only [box, Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · exact ⟨0, edge_sound h lower upper⟩
  · exact ⟨1, edge_sound h lower upper⟩
  · exact ⟨2, edge_sound h lower upper⟩
  · exact ⟨3, edge_sound h lower upper⟩
  · exact ⟨4, edge_sound h lower upper⟩

-- An edge passing on the whole box witnesses every point in it.
-- Otherwise fix the next coordinate and test each resulting smaller box.
def checkBox (a lo hi : Row) : List (Fin 5) → Bool
  | [] => box a lo hi
  | i :: rest => box a lo hi || allThrough (fun x =>
      checkBox a (Function.update lo i x) (Function.update hi i x) rest) (hi i)

lemma checkBox_sound {a t : Row} (indices : List (Fin 5)) {lo hi : Row}
    (h : checkBox a lo hi indices = true) (lower : lo ≤ t) (upper : t ≤ hi) :
    Good a t := by
  induction indices generalizing lo hi with
  | nil => exact box_sound h lower upper
  | cons i rest ih =>
    rcases Bool.or_eq_true_iff.mp h with hit | split
    · exact box_sound hit lower upper
    · apply ih (get split (upper i))
      · intro j
        by_cases e : j = i
        · simp [e]
        · simpa [Function.update_of_ne e] using lower j
      · intro j
        by_cases e : j = i
        · simp [e]
        · simpa [Function.update_of_ne e] using upper j

-- Rotate a smallest class into position zero. Subtract its size from each
-- class, leaving four nonnegative entries whose sum is 24 - 5*m.
def slice (p : Row → Bool) (m : ℕ) : Bool :=
  let r := 24 - 5*m
  allThrough (fun b => allThrough (fun c => allThrough (fun d =>
    p ![m, m+b, m+c, m+d, m+(r-b-c-d)]) (r-b-c)) (r-b)) r

lemma slice_sound {p : Row → Bool} (a : Row) (total : ∑ i, a i = 24)
    (least : ∀ i, a 0 ≤ a i) (h : slice p (a 0) = true) : p a = true := by
  rw [Fin.sum_univ_five] at total
  have h1 := least 1
  have h2 := least 2
  have h3 := least 3
  have h4 := least 4
  let m := a 0
  let r := 24 - 5*m
  have hb := get h (show a 1 - m ≤ r by dsimp [r, m]; omega)
  have hc := get hb (show a 2 - m ≤ r - (a 1-m) by dsimp [r, m]; omega)
  have hd := get hc (show a 3 - m ≤ r - (a 1-m) - (a 2-m) by dsimp [r, m]; omega)
  change p ![m, m+(a 1-m), m+(a 2-m), m+(a 3-m),
    m+(r-(a 1-m)-(a 2-m)-(a 3-m))] = true at hd
  have last : m+(r-(a 1-m)-(a 2-m)-(a 3-m)) = a 4 := by dsimp [r, m]; omega
  rw [last, show m+(a 1-m) = a 1 by dsimp [m]; omega,
    show m+(a 2-m) = a 2 by dsimp [m]; omega,
    show m+(a 3-m) = a 3 by dsimp [m]; omega] at hd
  convert hd using 2
  funext i
  fin_cases i <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate (m : ℕ) (positive : 1 ≤ m) (small : m ≤ 4) :
    slice (fun a => checkBox a (fun _ => 0) a [0, 1, 2, 3, 4]) m = true := by
  interval_cases m <;> decide +kernel

lemma least_good (a t : Row) (total : ∑ i, a i = 24) (upper : t ≤ a)
    (least : ∀ i, a 0 ≤ a i) : Good a t := by
  have sum := total
  rw [Fin.sum_univ_five] at sum
  by_cases zero : a 0 = 0
  · refine ⟨0, ?_⟩
    change a 0 * a 1 + min (t 0 + t 1 + t 3) (t 2 + t 4) ≤ 25 + t 0 * t 1
    rw [zero, zero_mul, zero_add]
    exact (min_le_right _ _).trans
      ((Nat.add_le_add (upper 2) (upper 4)).trans (by omega))
  · have small : a 0 ≤ 4 := by
      have := least 1; have := least 2; have := least 3; have := least 4; omega
    exact checkBox_sound _ (slice_sound a total least (certificate _ (by omega) small))
      (fun _ => Nat.zero_le _) upper

end FiveCycleBound

theorem OMA.solution : OMA.R_Erdos23_erdos_23_variants_n5_R3.H1 := by
  intro a t total upper
  obtain ⟨r, _, least⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  let b (i : Fin 5) := a (r+i)
  let u (i : Fin 5) := t (r+i)
  have rotated : ∑ i, b i = 24 :=
    (Fintype.sum_equiv (Equiv.addLeft r) b a (fun _ => rfl)).trans total
  have lb (i : Fin 5) : b 0 ≤ b i := by
    simpa [b] using least (r+i) (Finset.mem_univ _)
  obtain ⟨i, hi⟩ := FiveCycleBound.least_good b u rotated (fun j => upper (r+j)) lb
  exact ⟨r+i, by simpa [b, u, add_assoc] using hi⟩
