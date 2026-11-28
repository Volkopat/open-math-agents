import OMAStatements.S_oeis_a187173

/-!
A left-handed knight visiting three different squares makes two ordered moves.
Four straight move pairs fit bounding rectangles with coordinate spans 4 and 2.
The eight turning pairs have spans 3 and 2. For each shape, count all translations
inside the board. Natural subtraction handles boards too small for that shape.
-/

namespace OMA.A187173

open OMA.S_oeis_a187173

def Fits (n : ℕ) (u v z : ℤ) : Prop :=
  0 ≤ z ∧ z < n ∧ 0 ≤ z + u ∧ z + u < n ∧ 0 ≤ z + v ∧ z + v < n

def width (u v : ℤ) : ℕ := (max 0 (max u v) - min 0 (min u v)).toNat

abbrev DirPair := {ij : Fin 4 × Fin 4 // steps ij.1 + steps ij.2 ≠ 0}

abbrev Places (n : ℕ) (d : DirPair) :=
  {x : ℤ // Fits n (steps d.1.1).1 (steps d.1.1 + steps d.1.2).1 x} ×
    {y : ℤ // Fits n (steps d.1.1).2 (steps d.1.1 + steps d.1.2).2 y}

end OMA.A187173

namespace OMA.A187173

theorem fits_bounds (n : ℕ) (u v z : ℤ) :
    Fits n u v z ↔ -(min 0 (min u v)) ≤ z ∧ z < (n : ℤ) - max 0 (max u v) := by
  simp only [Fits, min_def, max_def]
  split_ifs <;> omega

def fitsEquiv (n : ℕ) (u v : ℤ) : {z : ℤ // Fits n u v z} ≃ Fin (n - width u v) := by
  let lo := min 0 (min u v)
  let hi := max 0 (max u v)
  have hl : lo ≤ 0 := min_le_left _ _
  have hh : 0 ≤ hi := le_max_left _ _
  have bounds (z : ℤ) : Fits n u v z ↔ -lo ≤ z ∧ z < (n : ℤ) - hi := fits_bounds n u v z
  change {z : ℤ // Fits n u v z} ≃ Fin (n - (hi - lo).toNat)
  refine {
    toFun := fun z => ⟨(z.val + lo).toNat, ?_⟩
    invFun := fun i => ⟨(i.val : ℤ) - lo, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have hb := (bounds z.val).mp z.property
    omega
  · apply (bounds _).mpr
    have hb := i.isLt
    omega
  · intro z
    apply Subtype.ext
    have hb := (bounds z.val).mp z.property
    change ((z.val + lo).toNat : ℤ) - lo = z.val
    omega
  · intro i
    apply Fin.ext
    change ((i.val : ℤ) - lo + lo).toNat = i.val
    simp

end OMA.A187173

namespace OMA.A187173

open OMA.S_oeis_a187173

private def location {n : ℕ} (q : Fin n × Fin n) : ℤ × ℤ := (q.1, q.2)

private theorem location_injective {n : ℕ} : Function.Injective (@location n) := by
  intro a b h
  exact Prod.ext (Fin.ext (Int.ofNat_inj.mp (congrArg Prod.fst h)))
    (Fin.ext (Int.ofNat_inj.mp (congrArg Prod.snd h)))

private theorem delta_sum {n : ℕ} (p : Fin 3 → Fin n × Fin n) :
    delta p 0 + delta p 1 = location (p 2) - location (p 0) := by
  change (location (p 1) - location (p 0)) + (location (p 2) - location (p 1)) = _
  abel

private theorem injective_iff_deltas {n : ℕ} (p : Fin 3 → Fin n × Fin n) :
    Function.Injective p ↔ delta p 0 ≠ 0 ∧ delta p 1 ≠ 0 ∧ delta p 0 + delta p 1 ≠ 0 := by
  rw [delta_sum]
  change Function.Injective p ↔ location (p 1) - location (p 0) ≠ 0 ∧
    location (p 2) - location (p 1) ≠ 0 ∧ location (p 2) - location (p 0) ≠ 0
  simp only [sub_ne_zero, ne_eq, location_injective.eq_iff]
  constructor
  · intro h
    exact ⟨fun e => (by decide : (1 : Fin 3) ≠ 0) (h e),
      fun e => (by decide : (2 : Fin 3) ≠ 1) (h e), fun e => (by decide : (2 : Fin 3) ≠ 0) (h e)⟩
  · rintro ⟨h10, h21, h20⟩ i j he
    fin_cases i <;> fin_cases j <;> tauto

private theorem step_injective : Function.Injective steps := by decide
private theorem step_ne_zero (d : Fin 4) : steps d ≠ 0 := by fin_cases d <;> decide
private theorem step_allowed (d : Fin 4) : IsStep (steps d) := by fin_cases d <;> simp [IsStep]
private theorem dir_of_step {u : ℤ × ℤ} (h : IsStep u) : ∃ d, u = steps d := by
  rcases h with h | h | h | h
  exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]

private def coord {n : ℕ} (z : ℤ) (h : 0 ≤ z ∧ z < n) : Fin n := ⟨z.toNat, by omega⟩
private theorem coord_val {n : ℕ} (z : ℤ) (h : 0 ≤ z ∧ z < n) : ((coord z h : ℕ) : ℤ) = z :=
  Int.toNat_of_nonneg h.1

private def along {n : ℕ} {u v : ℤ} (s : {z : ℤ // Fits n u v z}) : Fin 3 → Fin n :=
  ![coord s.1 ⟨s.2.1, s.2.2.1⟩, coord (s.1 + u) ⟨s.2.2.2.1, s.2.2.2.2.1⟩,
    coord (s.1 + v) s.2.2.2.2.2]

private def positions {n : ℕ} (s : (d : DirPair) × Places n d) (i : Fin 3) : Fin n × Fin n :=
  (along s.2.1 i, along s.2.2 i)

private theorem at_zero {n : ℕ} (s : (d : DirPair) × Places n d) :
    location (positions s 0) = (s.2.1.1, s.2.2.1) := by
  exact Prod.ext (coord_val _ ⟨s.2.1.2.1, s.2.1.2.2.1⟩) (coord_val _ ⟨s.2.2.2.1, s.2.2.2.2.1⟩)

private theorem at_one {n : ℕ} (s : (d : DirPair) × Places n d) :
    location (positions s 1) = (s.2.1.1, s.2.2.1) + steps s.1.1.1 := by
  exact Prod.ext (coord_val _ ⟨s.2.1.2.2.2.1, s.2.1.2.2.2.2.1⟩) (coord_val _ ⟨s.2.2.2.2.2.1, s.2.2.2.2.2.2.1⟩)

private theorem at_two {n : ℕ} (s : (d : DirPair) × Places n d) :
    location (positions s 2) = (s.2.1.1, s.2.2.1) + (steps s.1.1.1 + steps s.1.1.2) := by
  exact Prod.ext (coord_val _ s.2.1.2.2.2.2.2) (coord_val _ s.2.2.2.2.2.2.2)

private theorem first_move {n : ℕ} (s : (d : DirPair) × Places n d) :
    delta (positions s) 0 = steps s.1.1.1 := by
  change location (positions s 1) - location (positions s 0) = _
  rw [at_one, at_zero]
  abel

private theorem second_move {n : ℕ} (s : (d : DirPair) × Places n d) :
    delta (positions s) 1 = steps s.1.1.2 := by
  change location (positions s 2) - location (positions s 1) = _
  rw [at_two, at_one]
  abel

private def placeTour {n : ℕ} (s : (d : DirPair) × Places n d) : Tour n := by
  refine ⟨positions s, (injective_iff_deltas _).2 ?_, ?_⟩
  · rw [first_move, second_move]
    exact ⟨step_ne_zero _, step_ne_zero _, s.1.2⟩
  · intro i
    fin_cases i
    · change IsStep (delta (positions s) 0)
      rw [first_move]
      exact step_allowed _
    · change IsStep (delta (positions s) 1)
      rw [second_move]
      exact step_allowed _

private theorem placeTour_injective {n : ℕ} : Function.Injective (@placeTour n) := by
  rintro ⟨d, s⟩ ⟨e, t⟩ h
  have heq := congrArg Subtype.val h
  change positions ⟨d, s⟩ = positions ⟨e, t⟩ at heq
  have h1 := congrArg (fun p => delta p 0) heq
  have h2 := congrArg (fun p => delta p 1) heq
  simp only [first_move, second_move] at h1 h2
  have : d = e := Subtype.ext (Prod.ext (step_injective h1) (step_injective h2))
  subst e
  have h0 := congrArg (fun p => location (p 0)) heq
  simp only [at_zero] at h0
  have : s = t := Prod.ext (Subtype.ext (congrArg Prod.fst h0)) (Subtype.ext (congrArg Prod.snd h0))
  subst t
  rfl

private theorem fits_of_points {n : ℕ} (x y z : Fin n) (u v : ℤ)
    (hy : (y : ℤ) = x + u) (hz : (z : ℤ) = x + v) : Fits n u v x := by
  unfold Fits
  rw [← hy, ← hz]
  omega

private theorem placeTour_surjective {n : ℕ} : Function.Surjective (@placeTour n) := by
  intro ⟨p, inj, moves⟩
  obtain ⟨a, ha⟩ := dir_of_step (moves 0)
  obtain ⟨b, hb⟩ := dir_of_step (moves 1)
  let d : DirPair := ⟨(a,b), by simpa only [← ha, ← hb] using ((injective_iff_deltas p).1 inj).2.2⟩
  have h1 : location (p 1) = location (p 0) + steps a := by
    change location (p 1) - location (p 0) = steps a at ha
    rw [← ha]
    abel
  have h2 : location (p 2) = location (p 0) + (steps a + steps b) := by
    rw [← ha, ← hb, delta_sum]
    abel
  let s : Places n d :=
    (⟨_, fits_of_points (p 0).1 (p 1).1 (p 2).1 _ _ (congrArg Prod.fst h1) (congrArg Prod.fst h2)⟩,
     ⟨_, fits_of_points (p 0).2 (p 1).2 (p 2).2 _ _ (congrArg Prod.snd h1) (congrArg Prod.snd h2)⟩)
  refine ⟨⟨d, s⟩, Subtype.ext ?_⟩
  change positions ⟨d, s⟩ = p
  funext i
  apply location_injective
  fin_cases i
  · exact at_zero _
  · exact (at_one _).trans h1.symm
  · exact (at_two _).trans h2.symm

noncomputable def tourEquiv (n : ℕ) : Tour n ≃ ((d : DirPair) × Places n d) :=
  (Equiv.ofBijective placeTour ⟨placeTour_injective, placeTour_surjective⟩).symm

end OMA.A187173

namespace OMA.A187173

open OMA.S_oeis_a187173

theorem count_from_equiv (n : ℕ) (h : Tour n ≃ ((d : DirPair) × Places n d)) :
    a n = 4 * (n - 4) * (n - 2) + 8 * (n - 3) * (n - 2) := by
  let x (d : Fin 4 × Fin 4) := n - width (steps d.1).1 (steps d.1 + steps d.2).1
  let y (d : Fin 4 × Fin 4) := n - width (steps d.1).2 (steps d.1 + steps d.2).2
  let boxes (d : DirPair) : Places n d ≃ Fin (x d.val) × Fin (y d.val) :=
    Equiv.prodCongr (fitsEquiv n _ _) (fitsEquiv n _ _)
  have total (f : Fin 4 × Fin 4 → ℕ) : (∑ d : DirPair, f d.val) =
      ∑ d : Fin 4 × Fin 4, if steps d.1 + steps d.2 ≠ 0 then f d else 0 := by
    rw [← Finset.sum_filter]
    symm
    exact Finset.sum_subtype _ (by simp) f
  rw [a, Nat.card_congr (h.trans (Equiv.sigmaCongrRight boxes)), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [total (fun d => x d * y d), Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four]
  norm_num [x, y, steps, width, Prod.ext_iff]
  ring_nf <;> rfl

end OMA.A187173

namespace OMA.A187173

open PowerSeries S_oeis_a187173

lemma identities_of_count
    (ha : ∀ n : ℕ, a n = 4 * (n - 4) * (n - 2) + 8 * (n - 3) * (n - 2)) :
    type_of% @OMA.S_oeis_a187173.main := by
  have hquad (n : ℕ) (hn : 3 < n) :
      (a n : ℤ) = 12 * (n : ℤ) ^ 2 - 64 * (n : ℤ) + 80 := by
    rw [ha]
    push_cast [Nat.cast_sub (show 4 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega),
      Nat.cast_sub (show 2 ≤ n by omega)]
    ring
  refine ⟨?_, hquad⟩
  let F := PowerSeries.mk (fun n => (a n : ℤ))
  change F * (1 - X) ^ 3 = _
  have hleft : F * (1 - X) ^ 3 =
      F - C (3 : ℤ) * (F * X ^ 1) + C (3 : ℤ) * (F * X ^ 2) - F * X ^ 3 := by
    norm_num
    ring
  have hright : 4 * X ^ 4 * (4 - X) * (1 + X) =
      C (16 : ℤ) * X ^ 4 + C (12 : ℤ) * X ^ 5 - C (4 : ℤ) * X ^ 6 := by
    norm_num
    ring
  rw [hleft, hright]
  ext n
  simp only [map_add, map_sub, coeff_C_mul]
  simp only [coeff_mul_X_pow', coeff_X_pow, F, coeff_mk]
  by_cases hn : n < 7
  · interval_cases n <;> norm_num [ha]
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega)]
    rw [hquad n (by omega), hquad (n - 1) (by omega), hquad (n - 2) (by omega),
      hquad (n - 3) (by omega)]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
      Nat.cast_sub (show 3 ≤ n by omega)]
    ring

end OMA.A187173

theorem OMA.solution : type_of% @OMA.S_oeis_a187173.main :=
  OMA.A187173.identities_of_count (fun n => OMA.A187173.count_from_equiv n (OMA.A187173.tourEquiv n))
