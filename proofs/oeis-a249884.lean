import OMAStatements.S_oeis_a249884

namespace A249884Proof

open OMA.S_oeis_a249884

def Split {n : ℕ} (x : Fin 7 → Fin (n+1)) (S : Finset (Fin 7)) (m : ℕ) : Prop :=
  S.card = 3 ∧ (∀ i ∈ S, (x i : ℕ) ≤ m) ∧ (∃ i ∈ S, (x i : ℕ) = m) ∧
    (∀ i ∉ S, m < (x i : ℕ))

instance {n : ℕ} (x : Fin 7 → Fin (n+1)) (S : Finset (Fin 7)) (m : ℕ) :
    Decidable (Split x S m) := by unfold Split; infer_instance

private theorem good_iff {n : ℕ} (x : Fin 7 → Fin (n+1)) : good x = true ↔
    ¬ (∃ S : Finset (Fin 7), S.card = 3 ∧ ∃ v < n+1,
      (∀ t ∈ S, (x t : ℕ) ≤ v) ∧ (∃ t ∈ S, (x t : ℕ) = v) ∧
      (∀ t ∉ S, v ≤ (x t : ℕ)) ∧ (∃ t ∉ S, (x t : ℕ) = v)) := by
  simp [good, Finset.mem_powersetCard, OMA.S_oeis_a249884.get]

/-- A strict cut and any weak cut at the same rank have the same set of lower indices. -/
private theorem cut_eq {n : ℕ} (x : Fin 7 → Fin (n+1)) {S T : Finset (Fin 7)}
    (hc : S.card = T.card)
    (hs : ∀ i ∈ S, ∀ j ∉ S, (x i : ℕ) < (x j : ℕ))
    (ht : ∀ i ∈ T, ∀ j ∉ T, (x i : ℕ) ≤ (x j : ℕ)) : S = T := by
  by_contra h
  have hst : ¬ S ⊆ T := fun hsub => h (Finset.eq_of_subset_of_card_le hsub hc.ge)
  have hts : ¬ T ⊆ S := fun hsub => h (Finset.eq_of_subset_of_card_le hsub hc.le).symm
  simp only [Finset.subset_iff, not_forall, exists_prop] at hst hts
  obtain ⟨i,hi,hni⟩ := hst
  obtain ⟨j,hj,hnj⟩ := hts
  exact (not_lt_of_ge (ht j hj i hni)) (hs i hi j hnj)

theorem split_sound {n : ℕ} {x : Fin 7 → Fin (n+1)} {S m}
    (h : Split x S m) : good x = true := by
  rcases h with ⟨hs,hin,_,hout⟩
  apply (good_iff x).mpr
  rintro ⟨T,ht,v,_,htin,⟨i,hi,hxi⟩,htout,⟨j,hj,hxj⟩⟩
  have he : S = T := cut_eq x (hs.trans ht.symm)
    (fun i hi j hj => lt_of_le_of_lt (hin i hi) (hout j hj))
    (fun i hi j hj => le_trans (htin i hi) (htout j hj))
  subst T
  have hlt := lt_of_le_of_lt (hin i hi) (hout j hj)
  omega

private theorem split_uniq {n : ℕ} {x : Fin 7 → Fin (n+1)}
    {p q : Finset (Fin 7) × Fin (n+1)} (hp : Split x p.1 p.2) (hq : Split x q.1 q.2) :
    p = q := by
  obtain ⟨S,m⟩ := p
  obtain ⟨T,k⟩ := q
  rcases hp with ⟨hs,hsin,⟨i,hi,hxi⟩,hsout⟩
  rcases hq with ⟨ht,htin,⟨j,hj,hxj⟩,htout⟩
  have he : S = T := cut_eq x (hs.trans ht.symm)
    (fun i hi j hj => lt_of_le_of_lt (hsin i hi) (hsout j hj))
    (fun i hi j hj => le_trans (htin i hi) (htout j hj).le)
  subst T
  have ha := hsin j hj
  have hb := htin i hi
  have hmk : m = k := Fin.ext (by dsimp at ha hb hxi hxj; omega)
  rw [hmk]

private theorem split_exists {n : ℕ} (x : Fin 7 → Fin (n+1)) (hx : good x = true) :
    ∃ p : Finset (Fin 7) × Fin (n+1), Split x p.1 p.2 := by
  let π := Tuple.sort x
  let B : Finset (Fin 7) := {0, 1, 2}
  let S := B.map π.toEmbedding
  let m := x (π 2)
  have hB : ∀ i : Fin 7, i ∈ B ↔ i ≤ 2 := by
    change ∀ i : Fin 7, i ∈ ({0,1,2} : Finset _) ↔ i ≤ 2
    decide
  have hmem (i : Fin 7) : π i ∈ S ↔ i ≤ 2 := by
    rw [← hB]
    change π.toEmbedding i ∈ B.map π.toEmbedding ↔ i ∈ B
    simp
  have hcard : S.card = 3 := by
    rw [show S.card = B.card by exact Finset.card_map _]
    decide
  have hin : ∀ i ∈ S, (x i : ℕ) ≤ m.val := by
    intro i hi
    obtain ⟨j,rfl⟩ := π.surjective i
    exact Tuple.monotone_sort x ((hmem j).mp hi)
  have hmax : ∃ i ∈ S, (x i : ℕ) = m.val := ⟨π 2, (hmem 2).mpr le_rfl, rfl⟩
  have hout : ∀ i ∉ S, m.val ≤ (x i : ℕ) := by
    intro i hi
    obtain ⟨j,rfl⟩ := π.surjective i
    exact Tuple.monotone_sort x (le_of_lt (lt_of_not_ge (fun h => hi ((hmem j).mpr h))))
  refine ⟨(S,m), hcard, hin, hmax, ?_⟩
  intro i hi
  apply lt_of_le_of_ne (hout i hi)
  intro he
  exact (good_iff x).mp hx ⟨S,hcard,m.val,m.isLt,hin,hmax,hout,i,hi,he.symm⟩

theorem split_good {n : ℕ} (x : Fin 7 → Fin (n+1)) :
    good x = true ↔ ∃! p : Finset (Fin 7) × Fin (n+1), Split x p.1 p.2.val := by
  constructor
  · intro h
    obtain ⟨p,hp⟩ := split_exists x h
    exact ⟨p,hp,fun _ hq => split_uniq hq hp⟩
  · rintro ⟨p,hp,_⟩
    exact split_sound hp

open Finset

private def choices {n : ℕ} (S : Finset (Fin 7)) (L H : Finset (Fin (n+1))) :
    Finset (Fin 7 → Fin (n+1)) :=
  Fintype.piFinset (fun i => if i ∈ S then L else H)

private theorem choices_mem {n : ℕ} {x : Fin 7 → Fin (n+1)} {S : Finset (Fin 7)}
    {L H : Finset (Fin (n+1))} : x ∈ choices S L H ↔
    (∀ i ∈ S, x i ∈ L) ∧ (∀ i ∉ S, x i ∈ H) := by
  rw [choices, Fintype.mem_piFinset]
  constructor
  · intro h
    exact ⟨fun i hi => by simpa [hi] using h i, fun i hi => by simpa [hi] using h i⟩
  · rintro ⟨hL,hH⟩ i
    by_cases hi : i ∈ S <;> simp [hi, hL, hH]

private theorem choices_card {n : ℕ} (S : Finset (Fin 7)) (hS : S.card = 3)
    (L H : Finset (Fin (n+1))) : (choices S L H).card = L.card^3 * H.card^4 := by
  rw [choices, Fintype.card_piFinset, ← prod_mul_prod_compl S]
  have hL (i : Fin 7) (hi : i ∈ S) : (if i ∈ S then L else H).card = L.card := by simp [hi]
  have hH (i : Fin 7) (hi : i ∈ Sᶜ) : (if i ∈ S then L else H).card = H.card := by
    simp [mem_compl.mp hi]
  simp only [prod_congr rfl hL, prod_congr rfl hH, prod_const, card_compl, Fintype.card_fin, hS]

theorem split_card (n : ℕ) (S : Finset (Fin 7)) (m : Fin (n+1)) (hS : S.card = 3) :
    (univ.filter (fun x : Fin 7 → Fin (n+1) => Split x S m.val)).card =
      ((m.val+1)^3-m.val^3)*(n-m.val)^4 := by
  have hsub : choices S (Iio m) (Ioi m) ⊆ choices S (Iic m) (Ioi m) := by
    intro x hx
    obtain ⟨hL,hH⟩ := choices_mem.mp hx
    exact choices_mem.mpr ⟨fun i hi => Iio_subset_Iic_self (hL i hi), hH⟩
  have heq : univ.filter (fun x : Fin 7 → Fin (n+1) => Split x S m.val) =
      choices S (Iic m) (Ioi m) \ choices S (Iio m) (Ioi m) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, choices_mem, mem_Iic, mem_Iio,
      mem_Ioi, Fin.le_def, Fin.lt_def, Split, hS, true_and]
    constructor
    · rintro ⟨hL,⟨i,hi,hx⟩,hH⟩
      exact ⟨⟨hL,hH⟩, fun h => (ne_of_lt (h.1 i hi)) hx⟩
    · rintro ⟨⟨hL,hH⟩,hne⟩
      refine ⟨hL, ?_, hH⟩
      by_contra! h
      exact hne ⟨fun i hi => lt_of_le_of_ne (hL i hi) (h i hi), hH⟩
  rw [heq, card_sdiff_of_subset hsub, choices_card S hS, choices_card S hS,
    Fin.card_Iic, Fin.card_Iio, Fin.card_Ioi, Nat.sub_mul, Nat.add_sub_cancel]

private theorem count_by_split (n : ℕ) :
    (a n : ℚ) = 35*∑ m ∈ Finset.range (n+1),
        (((m:ℚ)+1)^3-(m:ℚ)^3)*((n:ℚ)-m)^4 := by
  classical
  let P := Finset (Fin 7) × Fin (n+1)
  let f (x : Fin 7 → Fin (n+1)) (p : P) : ℕ :=
    if Split x p.1 p.2.val then 1 else 0
  have each (x : Fin 7 → Fin (n+1)) :
      (∑ p : P, f x p) = if good x = true then 1 else 0 := by
    by_cases hx : good x = true
    · obtain ⟨p, hp, hu⟩ := (split_good x).mp hx
      rw [Finset.sum_eq_single p]
      · simp [f, hp, hx]
      · intro q _ hq
        exact if_neg (fun h => hq (hu q h))
      · simp
    · have no (p : P) : ¬ Split x p.1 p.2.val := fun h => hx (split_sound h)
      simp [f, no, hx]
  let g (m : Fin (n+1)) : ℕ := ((m.val+1)^3-m.val^3)*(n-m.val)^4
  have fixed (S : Finset (Fin 7)) (m : Fin (n+1)) :
      (∑ x, f x (S,m)) = if S.card=3 then g m else 0 := by
    change (∑ x : Fin 7 → Fin (n+1), if Split x S m.val then 1 else 0) = _
    rw [Finset.sum_boole]
    split_ifs with hs
    · exact split_card n S m hs
    · simp [Split, hs]
  have num : (∑ S : Finset (Fin 7), if S.card=3 then (1:ℕ) else 0) = 35 := by
    decide +kernel
  have eqn : ((Finset.univ : Finset (Fin 7 → Fin (n+1))).filter (fun x => good x)).card =
      35 * ∑ m : Fin (n+1), g m := by
    rw [Finset.card_filter]
    change (∑ x : Fin 7 → Fin (n+1), if good x = true then 1 else 0) = _
    simp_rw [← each]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    simp only [fixed, Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [← num, Finset.sum_mul]
    simp only [ite_mul, one_mul, zero_mul]
  change ((↑((Finset.univ : Finset (Fin 7 → Fin (n+1))).filter (fun x => good x)).card : ℤ) : ℚ) = _
  rw [eqn]
  push_cast
  change 35 * (∑ m : Fin (n+1), (g m : ℚ)) = _
  apply congrArg (fun z : ℚ => 35*z)
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro m _
  have hm : m.val ≤ n := by omega
  have hc : m.val^3 ≤ (m.val+1)^3 := Nat.pow_le_pow_left (by omega) 3
  simp [g, Nat.cast_sub hm, Nat.cast_sub hc]

end A249884Proof

namespace A249884Proof

open OMA.S_oeis_a249884 PowerSeries

private abbrev U : ℚ⟦X⟧ := mk fun m : ℕ => ((m : ℚ) + 1)^3 - (m : ℚ)^3
private abbrev V : ℚ⟦X⟧ := mk fun m : ℕ => (m : ℚ)^4

private theorem cubeDifferenceSeries : U*(1-X)^3 = 1+4*X+X^2 := by
  rw [show U*(1-X)^3 = U-C 3*(U*X^1)+C 3*(U*X^2)-U*X^3 by simp only [map_ofNat]; ring,
      show (1+4*X+X^2 : ℚ⟦X⟧) = X^0+C 4*X^1+X^2 by simp only [map_ofNat]; ring]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow, coeff_mul_X_pow', U, coeff_mk]
  by_cases hn : n < 3
  · interval_cases n <;> norm_num
  · simp (disch := omega) only [coeff_C, if_pos, if_neg, Nat.cast_sub, Nat.cast_ofNat, Nat.cast_one]
    ring

private theorem fourthPowerSeries : V*(1-X)^5 = X*(1+X)*(1+10*X+X^2) := by
  rw [show V*(1-X)^5 = V-C 5*(V*X^1)+C 10*(V*X^2)-C 10*(V*X^3)+C 5*(V*X^4)-V*X^5 by
        simp only [map_ofNat]; ring,
      show (X : ℚ⟦X⟧)*(1+X)*(1+10*X+X^2) = X^1+C 11*X^2+C 11*X^3+X^4 by
        simp only [map_ofNat]; ring]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow, coeff_mul_X_pow', V, coeff_mk]
  by_cases hn : n < 5
  · interval_cases n <;> norm_num
  · simp (disch := omega) only [coeff_C, if_pos, if_neg, Nat.cast_sub, Nat.cast_ofNat, Nat.cast_one]
    ring

theorem seriesFromCount (count : ∀ n : ℕ, (a n : ℚ) = 35*∑ m ∈ Finset.range (n+1),
    (((m:ℚ)+1)^3-(m:ℚ)^3)*((n:ℚ)-m)^4) :
    (mk (fun n => if n < 1 then 0 else (a n : ℚ)) * (1-X)^8 =
       35*X*(1+X)*(1+4*X+X^2)*(1+10*X+X^2)) ∧
    (∀ n : ℕ, 9 ≤ n → (a n : ℚ) = 8*a (n-1)-28*a (n-2)+56*a (n-3)-70*a (n-4)
      +56*a (n-5)-28*a (n-6)+8*a (n-7)-a (n-8)) := by
  let A : ℚ⟦X⟧ := mk fun n => if n < 1 then 0 else (a n : ℚ)
  have prod : A = C 35*(U*V) := by
    ext n
    rw [coeff_C_mul, coeff_mul]
    simp only [A, coeff_mk, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, U, V]
    by_cases hn : n = 0
    · subst n
      norm_num
    · rw [if_neg (by omega), count]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      rw [Nat.cast_sub (by simpa using Finset.mem_range.mp hm : m ≤ n)]
  have gf : A*(1-X)^8 = 35*X*(1+X)*(1+4*X+X^2)*(1+10*X+X^2) := by
    calc
      _ = C 35*((U*(1-X)^3)*(V*(1-X)^5)) := by rw [prod]; ring
      _ = _ := by rw [cubeDifferenceSeries, fourthPowerSeries]; simp only [map_ofNat]; ring
  refine ⟨gf, ?_⟩
  intro n hn
  rw [show A*(1-X)^8 = A-C 8*(A*X^1)+C 28*(A*X^2)-C 56*(A*X^3)+C 70*(A*X^4)
        -C 56*(A*X^5)+C 28*(A*X^6)-C 8*(A*X^7)+A*X^8 by simp only [map_ofNat]; ring,
      show 35*(X : ℚ⟦X⟧)*(1+X)*(1+4*X+X^2)*(1+10*X+X^2) =
        C 35*X^1+C 525*X^2+C 1960*X^3+C 1960*X^4+C 525*X^5+C 35*X^6 by
        simp only [map_ofNat]; ring] at gf
  have hc := congrArg (coeff (R := ℚ) n) gf
  simp (disch := omega) only [map_add, map_sub, coeff_C_mul,
    coeff_mul_X_pow', A, coeff_mk, coeff_C, if_pos, if_neg, add_zero] at hc
  linarith

end A249884Proof

open A249884Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a249884.main :=
  seriesFromCount count_by_split
