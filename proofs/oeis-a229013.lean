import OMAStatements.S_oeis_a229013

/-!
A boundary median forces the two outer letters of its window to equal that
boundary. This excludes six families of triples. Five explicit input words
realize every remaining triple.
-/

namespace MedianWindows

open OMA.S_oeis_a229013 Finset

private def outputs (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((univ.filter (fun x : Fin 5 → Fin (n + 1) => NoAdjEq x)).image medians)

private def Good (n x y z : ℕ) : Prop :=
  ¬ (x = 0 ∧ y = 0) ∧ ¬ (y = 0 ∧ z = 0) ∧
  ¬ (x = n ∧ y = n) ∧ ¬ (y = n ∧ z = n) ∧
  ¬ (x = 0 ∧ z = n) ∧ ¬ (x = n ∧ z = 0)

private lemma med_zero {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) :
    med3 a b c = 0 ↔ a = 0 ∧ c = 0 := by
  unfold med3
  omega

private lemma med_top {n a b c : ℕ} (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n)
    (hab : a ≠ b) (hbc : b ≠ c) : med3 a b c = n ↔ a = n ∧ c = n := by
  unfold med3
  omega

private lemma med_le {n a b c : ℕ} (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) :
    med3 a b c ≤ n := by
  unfold med3
  omega

private lemma sound {n a b c d e : ℕ} (hn : 0 < n)
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n) (he : e ≤ n)
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) :
    Good n (med3 a b c) (med3 b c d) (med3 c d e) := by
  simp only [Good, med_zero hab hbc, med_zero hbc hcd, med_zero hcd hde,
    med_top ha hb hc hab hbc, med_top hb hc hd hbc hcd, med_top hc hd he hcd hde]
  omega

private lemma realize {n a b c d e x y z : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n) (he : e ≤ n)
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e)
    (h₁ : med3 a b c = x) (h₂ : med3 b c d = y) (h₃ : med3 c d e = z) :
    (x,y,z) ∈ outputs n := by
  let v : Fin 5 → Fin (n+1) :=
    ![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩, ⟨d, by omega⟩, ⟨e, by omega⟩]
  refine mem_image.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> simp_all [v, Fin.ext_iff]
  · simp [medians, v, h₁, h₂, h₃]

private lemma complete {n x y z : ℕ} (hn : 0 < n) (hx : x ≤ n) (hy : y ≤ n)
    (hz : z ≤ n) (hg : Good n x y z) : (x,y,z) ∈ outputs n := by
  have cases' : (0 < x ∧ y < z) ∨ (x < n ∧ z < y) ∨
      (0 < x ∧ 0 < y ∧ y < n ∧ z = y) ∨ (x = 0 ∧ 0 < y ∧ z < n) ∨
      (x = n ∧ y < n ∧ 0 < z) := by
    unfold Good at hg
    omega
  rcases cases' with h | h | h | h | h
  · apply realize (a:=x) (b:=0) (c:=n) (d:=y) (e:=z) <;> first | omega | (simp [med3]; omega)
  · apply realize (a:=x) (b:=n) (c:=0) (d:=y) (e:=z) <;> first | omega | (simp [med3]; omega)
  · apply realize (a:=x) (b:=0) (c:=n) (d:=y) (e:=0) <;> first | omega | (simp [med3]; omega)
  · apply realize (a:=0) (b:=y) (c:=0) (d:=n) (e:=z) <;> first | omega | (simp [med3]; omega)
  · apply realize (a:=n) (b:=y) (c:=n) (d:=0) (e:=z) <;> first | omega | (simp [med3]; omega)

private lemma mem_outputs {n x y z : ℕ} (hn : 0 < n) :
    (x,y,z) ∈ outputs n ↔ x ≤ n ∧ y ≤ n ∧ z ≤ n ∧ Good n x y z := by
  constructor
  · intro h
    obtain ⟨v,hv,he⟩ := mem_image.mp h
    have hA := (mem_filter.mp hv).2
    have ne (i : Fin 4) : (v i.castSucc).val ≠ (v i.succ).val :=
      fun h => hA i (Fin.ext h)
    obtain ⟨rfl,rfl,rfl⟩ : med3 (v 0) (v 1) (v 2) = x ∧
        med3 (v 1) (v 2) (v 3) = y ∧ med3 (v 2) (v 3) (v 4) = z := by
      simpa [medians] using he
    have le (i : Fin 5) : (v i).val ≤ n := Nat.le_of_lt_succ (v i).isLt
    exact ⟨med_le (le 0) (le 1) (le 2), med_le (le 1) (le 2) (le 3),
      med_le (le 2) (le 3) (le 4),
      sound hn (le 0) (le 1) (le 2) (le 3) (le 4) (ne 0) (ne 1) (ne 2) (ne 3)⟩
  · rintro ⟨hx,hy,hz,hg⟩
    exact complete hn hx hy hz hg


private def pairs (n y : ℕ) : Finset (ℕ × ℕ) :=
  if y = 0 then Icc 1 n ×ˢ Icc 1 n
  else if y = n then range n ×ˢ range n
  else (((range (n+1) ×ˢ range (n+1)).erase (0,n)).erase (n,0))

private lemma mem_pairs {n x y z : ℕ} (hn : 0 < n) (_hy : y ≤ n) :
    (x,z) ∈ pairs n y ↔ x ≤ n ∧ z ≤ n ∧ Good n x y z := by
  by_cases h₀ : y = 0
  · simp [pairs, h₀, Good, hn.ne]
    omega
  by_cases hₙ : y = n
  · simp [pairs, hₙ, Good, hn.ne']
    omega
  · simp [pairs, h₀, hₙ, Good]
    omega

private lemma middle_count {n y : ℕ} (hn : 0 < n) (hy : y ≤ n) :
    ((outputs n).filter (fun t => t.2.1 = y)).card = (pairs n y).card := by
  apply card_bij (fun t _ => (t.1,t.2.2))
  · rintro ⟨x,b,z⟩ h
    obtain ⟨hh,rfl⟩ := mem_filter.mp h
    obtain ⟨hx,_,hz,hg⟩ := (mem_outputs hn).mp hh
    exact (mem_pairs hn hy).mpr ⟨hx,hz,hg⟩
  · rintro ⟨x,b,z⟩ h₁ ⟨u,c,v⟩ h₂ he
    have hb := (mem_filter.mp h₁).2
    have hc := (mem_filter.mp h₂).2
    have ex := congrArg Prod.fst he
    have ez := congrArg Prod.snd he
    simp_all
  · rintro ⟨x,z⟩ hp
    obtain ⟨hx,hz,hg⟩ := (mem_pairs hn hy).mp hp
    exact ⟨(x,y,z), mem_filter.mpr ⟨(mem_outputs hn).mpr ⟨hx,hy,hz,hg⟩,rfl⟩,rfl⟩

private lemma pair_count {n : ℕ} (hn : 0 < n) (y : ℕ) :
    (pairs n y).card = if y = 0 ∨ y = n then n^2 else (n+1)^2-2 := by
  by_cases h₀ : y = 0
  · simp [pairs, h₀, Nat.card_Icc, pow_two]
  by_cases hₙ : y = n
  · simp [pairs, hₙ, hn.ne', pow_two]
  · have ha : (0,n) ∈ (range (n+1) ×ˢ range (n+1)) := by simp
    have hb : (n,0) ∈ (range (n+1) ×ˢ range (n+1)).erase (0,n) := by simp [hn.ne']
    simp only [pairs, h₀, hₙ, or_self, if_false, card_erase_of_mem hb,
      card_erase_of_mem ha, card_product, card_range, pow_two]
    omega

private theorem count {n : ℕ} (hn : 1 ≤ n) :
    (a n : ℤ) = (n : ℤ)^3 + 3*(n : ℤ)^2 - 3*n + 1 := by
  have fiber := sum_card_fiberwise_eq_card_filter
    (outputs n) (range (n+1)) (fun t => t.2.1)
  have all : (outputs n).filter (fun t => t.2.1 ∈ range (n+1)) = outputs n := by
    apply filter_eq_self.mpr
    rintro ⟨x,y,z⟩ h
    exact mem_range.mpr (Nat.lt_succ_of_le ((mem_outputs hn).mp h).2.1)
  rw [all] at fiber
  have h : a n = ∑ y ∈ range (n+1), (pairs n y).card := by
    change (outputs n).card = _
    rw [← fiber]
    apply sum_congr rfl
    intro y hy
    exact middle_count hn (Nat.le_of_lt_succ (mem_range.mp hy))
  simp_rw [pair_count hn] at h
  obtain ⟨k,rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  rw [sum_range_succ, sum_range_succ'] at h
  have inside (j : ℕ) (hj : j ∈ range k) : ¬ (j + 1 = 0 ∨ j + 1 = k + 1) := by
    have := mem_range.mp hj
    omega
  have mid : (∑ j ∈ range k, if j+1 = 0 ∨ j+1 = k+1 then (k+1)^2 else (k+1+1)^2-2) =
      k * ((k+1+1)^2-2) := by
    calc
      _ = ∑ _j ∈ range k, ((k+1+1)^2-2) := by
        apply sum_congr rfl
        intro j hj
        rw [if_neg (inside j hj)]
      _ = _ := by simp
  rw [mid] at h
  simp at h
  rw [h]
  have hl : 2 ≤ (k+1+1)^2 := by nlinarith
  push_cast [Nat.cast_sub hl]
  ring


private theorem countQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (n : ℚ)^3 + 3*(n : ℚ)^2 - 3*n + 1 := by
  exact_mod_cast count hn

private theorem backward (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 4*a (n-1) - 6*a (n-2) + 4*a (n-3) - a (n-4) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+5 := ⟨n-5, by omega⟩
  simp only [show k+5-1 = k+4 by omega, show k+5-2 = k+3 by omega,
    show k+5-3 = k+2 by omega, show k+5-4 = k+1 by omega]
  rw [count (by omega), count (by omega), count (by omega), count (by omega), count (by omega)]
  push_cast
  ring

open PowerSeries in
private theorem generating :
    mk (fun n => (a n : ℚ)) * (1-X)^4 = X*(2-X)*(1+4*X+X^2) := by
  let F := mk (fun n => (a n : ℚ))
  change F * _ = _
  suffices H : F - (4:ℕ) • (F*X^1) + (6:ℕ) • (F*X^2) - (4:ℕ) • (F*X^3) + F*X^4 =
      (2:ℕ) • (X^1 : PowerSeries ℚ) + (7:ℕ) • X^2 - (2:ℕ) • X^3 - X^4 by
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at H
    linear_combination H
  have az : a 0 = 0 := by decide
  have a1 : (a 1 : ℚ) = 2 := by
    convert countQ 1 (by decide) using 1
    norm_num
  have a2 : (a 2 : ℚ) = 15 := by
    convert countQ 2 (by decide) using 1
    norm_num
  have a3 : (a 3 : ℚ) = 46 := by
    convert countQ 3 (by decide) using 1
    norm_num
  have a4 : (a 4 : ℚ) = 101 := by
    convert countQ 4 (by decide) using 1
    norm_num
  ext n
  simp only [map_add, map_sub, map_nsmul]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, coeff_mul_X_pow', coeff_X_pow, F, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | k
  · norm_num [az]
  · norm_num [az, a1]
  · norm_num [az, a1, a2]
  · simp only [Nat.reduceAdd, Nat.reduceSub, az, a1, a2, a3]
    norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, az, a1, a2, a3, a4]
    norm_num
  have hr := congrArg (fun v : ℤ => (v : ℚ)) (backward (k+5) (by omega))
  push_cast at hr
  simp [show 1 ≤ k+5 by omega, show 2 ≤ k+5 by omega, show 3 ≤ k+5 by omega,
    show 4 ≤ k+5 by omega, show k+5 ≠ 2 by omega, show k+5 ≠ 3 by omega,
    show k+5 ≠ 4 by omega]
  linarith

theorem result : type_of% @OMA.S_oeis_a229013.main :=
  ⟨fun _ h => count h, generating, backward⟩

end MedianWindows

theorem OMA.solution : type_of% @OMA.S_oeis_a229013.main := MedianWindows.result
