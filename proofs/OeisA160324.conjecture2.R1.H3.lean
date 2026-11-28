import OMAReductions.R_OeisA160324_conjecture2_R1
import Mathlib

-- The first proof of this step was merged from #27384 by @ppleskov.

/- For m at least 66, sixteen orders produce 8+(2m+13)t. Two more
orders and the remaining zeros or ones supply every residue. -/
namespace OMA.SunPolygonalLarge

open OeisA160324 (polygonalNumber)

def value (s : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => polygonalNumber s x + value (s + 1) xs

def represents (s d n : ℕ) : Prop :=
  ∃ xs : List ℕ, xs.length = d ∧ value s xs = n

lemma value_append (s : ℕ) (xs ys : List ℕ) :
    value s (xs ++ ys) = value s xs + value (s + xs.length) ys := by
  induction xs generalizing s with
  | nil => simp [value]
  | cons x xs ih => simp [value, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma join {s d e n v : ℕ} (left : represents s d n) (right : represents (s+d) e v) :
    represents s (d+e) (n+v) := by
  obtain ⟨xs, hx, hnx⟩ := left
  obtain ⟨ys, hy, hvy⟩ := right
  exact ⟨xs ++ ys, by simp [hx, hy], by simp [value_append, hx, hnx, hvy]⟩

lemma zero_one (s d r : ℕ) (hr : r ≤ d) : represents s d r := by
  induction d generalizing s r with
  | zero =>
    have : r = 0 := by omega
    subst r
    exact ⟨[], rfl, rfl⟩
  | succ d ih =>
    cases r with
    | zero =>
      obtain ⟨xs, h, e⟩ := ih (s+1) 0 (by omega)
      exact ⟨0::xs, by simp [h], by simp [value, polygonalNumber, e]⟩
    | succ r =>
      obtain ⟨xs, h, e⟩ := ih (s+1) r (by omega)
      exact ⟨1::xs, by simp [h], by simp [value, polygonalNumber, e, Nat.add_comm]⟩

/-- Surround a block by any requested number of ones among the other positions. -/
lemma surround {s t i r c v : ℕ} (hi : i ≤ t) (hr : r ≤ t)
    (block : represents (s+i) c v) : represents s (t+c) (v+r) := by
  let u := min r i
  have hu : u ≤ i := Nat.min_le_right _ _
  have ur : u ≤ r := Nat.min_le_left _ _
  have rem : r-u ≤ t-i := by dsimp [u]; omega
  have left := zero_one s i u hu
  have right := zero_one (s+(i+c)) (t-i) (r-u) rem
  have h := join left (join block (by simpa [Nat.add_assoc] using right))
  convert h using 1 <;> omega

lemma at_two (s : ℕ) (hs : 2 ≤ s) : polygonalNumber s 2 = s := by
  simp [polygonalNumber]
  omega

lemma one_large (s t i r : ℕ) (hs : 2 ≤ s) (hi : i ≤ t) (hr : r ≤ t) :
    represents s (t+1) (s+i+r) := by
  apply surround hi hr
  exact ⟨[2], rfl, by simp [value, at_two, show 2 ≤ s+i by omega]⟩

lemma two_large (s t i r : ℕ) (hs : 2 ≤ s) (hi : i ≤ t) (hr : r ≤ t) :
    represents s (t+2) ((s+i+(s+i+1))+r) := by
  apply surround hi hr
  exact ⟨[2,2], rfl, by simp [value, at_two, show 2 ≤ s+i by omega, show 2 ≤ s+i+1 by omega]⟩

lemma twice_half (u : ℕ) : 2 * (((u+1)*u)/2) = (u+1)*u := by
  have h : 2 ∣ (u+1)*u := by
    rcases (show 2 ∣ u ∨ 2 ∣ u+1 by omega) with he | he
    · exact dvd_mul_of_dvd_right he _
    · exact dvd_mul_of_dvd_left he _
  omega

/-- Consecutive polygonal indices at orders four apart produce a square. -/
lemma pair_square (a x : ℕ) :
    polygonalNumber (a+2) (x+1) + polygonalNumber (a+6) x = (a+2)*x^2+1 := by
  cases x with
  | zero => simp [polygonalNumber]
  | succ u =>
    have h := twice_half u
    have h' := twice_half (u+1)
    simp only [polygonalNumber, Nat.add_sub_cancel, show a+6-2 = a+4 by omega]
    nlinarith only [h, h', congrArg (fun z : ℕ => a*z) h, congrArg (fun z : ℕ => a*z) h']

lemma square_block (a t : ℕ) : represents (a+2) 16 (8+(2*a+15)*t) := by
  obtain ⟨w,x,y,z, ht⟩ := Nat.sum_four_squares t
  refine ⟨[w+1,x+1,y+1,z+1,w,x,y,z,z+1,y+1,x+1,w+1,z,y,x,w], rfl, ?_⟩
  rw [← ht]
  dsimp only [value]
  nlinarith only [pair_square a w, pair_square (a+1) x, pair_square (a+2) y,
    pair_square (a+3) z, pair_square (a+8) z, pair_square (a+9) y,
    pair_square (a+10) x, pair_square (a+11) w]

lemma large_order (m n : ℕ) (hm : 66 ≤ m) : represents (m+1) m n := by
  by_cases hsmall : n ≤ m
  · exact zero_one (m+1) m n hsmall
  by_cases hmid : n < 2*m+43
  · let i := min (n-(m+1)) (m-1)
    have hi : i ≤ m-1 := Nat.min_le_right _ _
    have hr : n-(m+1+i) ≤ m-1 := by dsimp [i]; omega
    have h := one_large (m+1) (m-1) i (n-(m+1+i)) (by omega) hi hr
    convert h using 1 <;> (try dsimp [i]) <;> omega
  let k := 2*m+13
  let d := n-(2*m+43)
  let b := d % k
  let t := m-18
  let i := min (b/2) t
  have hb : b < k := Nat.mod_lt _ (by dsimp [k]; omega)
  have hi : i ≤ t := Nat.min_le_right _ _
  have hr : b-2*i ≤ t := by dsimp [i, t, k] at *; omega
  have hsum : 2*i+(b-2*i)=b := by dsimp [i]; omega
  have sq := square_block (m-1) (d/k)
  rw [show m-1+2=m+1 by omega, show 2*(m-1)+15=k by dsimp [k]; omega] at sq
  have tail := two_large (m+1+16) t i (b-2*i) (by omega) hi hr
  have both := join sq tail
  have eqn : b + k*(d/k) = d := Nat.mod_add_div d k
  convert both using 1 <;> dsimp [t, d] at * <;> omega

lemma value_fin (s : ℕ) (xs : List ℕ) :
    value s xs = ∑ i : Fin xs.length, polygonalNumber (s+(i:ℕ)) (xs.get i) := by
  induction xs generalizing s with
  | nil => simp [value]
  | cons x xs ih =>
    change value s (x::xs) = ∑ i : Fin (xs.length+1), polygonalNumber (s+(i:ℕ)) ((x::xs).get i)
    rw [Fin.sum_univ_succ]
    simpa [value, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (polygonalNumber s x + ·) (ih (s+1))

lemma to_catalog {m n : ℕ} (h : represents (m+1) m n) :
    ∃ x : Fin m → ℕ, n = ∑ i : Fin m, polygonalNumber (m+(i:ℕ)+1) (x i) := by
  obtain ⟨xs, hlen, hval⟩ := h
  subst m
  refine ⟨xs.get, ?_⟩
  rw [← hval]
  simpa only [Nat.add_right_comm] using (value_fin (xs.length+1) xs)

end OMA.SunPolygonalLarge

theorem OMA.solution : OMA.R_OeisA160324_conjecture2_R1.H3 := by
  intro m hm n
  exact OMA.SunPolygonalLarge.to_catalog (OMA.SunPolygonalLarge.large_order m n hm)
