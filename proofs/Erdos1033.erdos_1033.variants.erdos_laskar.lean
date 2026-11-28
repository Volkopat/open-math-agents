import FormalConjectures.ErdosProblems.«1033»

private def adj {a m : ℕ} (r : ℕ) :
    Fin a ⊕ (Fin m ⊕ Fin m) → Fin a ⊕ (Fin m ⊕ Fin m) → Prop
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr (.inl x), .inr (.inr y) => (y - x).1 < r
  | .inr (.inr y), .inr (.inl x) => (y - x).1 < r
  | _, _ => False

open SimpleGraph Finset Filter in
open scoped Classical in
theorem OMA.solution : type_of% @Erdos1033.erdos_1033.variants.erdos_laskar := by
  refine ⟨6, eventually_atTop.2 ⟨100, fun n hn => ?_⟩⟩
  let s := Real.sqrt 3
  have hs : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsL : 17 / 10 < s := by nlinarith
  have hsU : s < 7 / 4 := by nlinarith
  have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
  let m : ℕ := ⌊(n : ℝ) / (2 * s)⌋₊
  have hmlo : (m : ℝ) * (2 * s) ≤ n := (le_div_iff₀ (by linarith)).1 (Nat.floor_le (by positivity))
  have hmhi : (n : ℝ) < ((m : ℝ) + 1) * (2 * s) :=
    (div_lt_iff₀ (by linarith)).1 (Nat.lt_floor_add_one _)
  have hm8 : 8 ≤ m := Nat.le_floor ((le_div_iff₀ (by linarith)).2 (by push_cast; linarith))
  have hm8' : (8 : ℝ) ≤ m := by exact_mod_cast hm8
  have h2m : 2 * m ≤ n := by exact_mod_cast (show (2 : ℝ) * m ≤ n by nlinarith)
  have h4m : (n : ℝ) ≤ 4 * m := by nlinarith
  let a := n - 2 * m
  have ha : n = a + 2 * m := by dsimp [a]; omega
  have ha' : (n : ℝ) = a + 2 * m := by exact_mod_cast ha
  let r : ℕ := ⌊(7 - 4 * s) * m⌋₊ + 1
  have hrl : (7 - 4 * s) * m < r := by simpa [r] using Nat.lt_floor_add_one ((7 - 4 * s) * (m : ℝ))
  have hru : (r : ℝ) ≤ (7 - 4 * s) * m + 1 := by
    have hrp : 0 ≤ (7 - 4 * s) * (m : ℝ) := mul_nonneg (by linarith) (by positivity)
    simpa [r] using add_le_add_right (Nat.floor_le hrp) 1
  have hrm : r ≤ m := by exact_mod_cast (show (r : ℝ) ≤ m by nlinarith)
  have : NeZero m := ⟨by omega⟩
  let H : SimpleGraph (Fin a ⊕ (Fin m ⊕ Fin m)) :=
    ⟨adj r, ⟨fun u v h => by rcases u with u | u | u <;> rcases v with v | v | v <;> exact h⟩,
      ⟨fun u h => by rcases u with u | u | u <;> exact h⟩⟩
  have hci : Nat.card {v : Fin m // v.1 < r} = r := by
    rw [Nat.card_congr ⟨fun v => ⟨v.1.1, v.2⟩, fun v => ⟨Fin.castLE hrm v, v.2⟩,
      fun _ => rfl, fun _ => rfl⟩, Nat.card_fin]
  have hdeg (u : Fin a ⊕ (Fin m ⊕ Fin m)) :
      H.degree u = match u with | .inl _ => 2 * m | .inr _ => a + r := by
    have hsp {A B : Type} [Fintype A] [Fintype B] (p : A ⊕ B → Prop) :
        Nat.card {v // p v} = Nat.card {v : A // p (.inl v)} + Nat.card {v : B // p (.inr v)} := by
      rw [Nat.card_congr (Equiv.subtypeSum (p := p)), Nat.card_sum]
    rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    change Nat.card {v // H.Adj u v} = _; rw [hsp, hsp]
    rcases u with u | u | u
    · change Nat.card {_v : Fin a // False} +
        (Nat.card {_v : Fin m // True} + Nat.card {_v : Fin m // True}) = 2 * m
      simp [two_mul]
    · change Nat.card {_v : Fin a // True} +
        (Nat.card {_v : Fin m // False} + Nat.card {v : Fin m // (v - u).1 < r}) = a + r
      have h1 : Nat.card {v : Fin m // (v - u).1 < r} = r :=
        (Nat.card_congr (Equiv.subtypeEquiv (Equiv.subRight u) fun _ => Iff.rfl)).trans hci
      rw [h1]; simp
    · change Nat.card {_v : Fin a // True} +
        (Nat.card {v : Fin m // (u - v).1 < r} + Nat.card {_v : Fin m // False}) = a + r
      have h1 : Nat.card {v : Fin m // (u - v).1 < r} = r :=
        (Nat.card_congr (Equiv.subtypeEquiv (Equiv.subLeft u) fun _ => Iff.rfl)).trans hci
      rw [h1]; simp
  let e : Fin a ⊕ (Fin m ⊕ Fin m) ≃ Fin n :=
    (Fintype.equivFin _).trans (finCongr (by simp [ha, two_mul]))
  obtain ⟨G, hG⟩ : ∃ G : SimpleGraph (Fin n), H.comap e.symm = G := ⟨_, rfl⟩
  have iso : G ≃g H := hG ▸ Iso.comap e.symm H
  refine ⟨G, ?_, fun t ht => ?_⟩
  · have hedge : G.edgeFinset.card = 2 * m * a + m * r := by
      rw [iso.card_edgeFinset_eq]
      have hsum := H.sum_degrees_eq_twice_card_edges
      simp only [hdeg, Fintype.sum_sum_type, sum_const, card_univ, Fintype.card_sum,
        Fintype.card_fin, smul_eq_mul] at hsum
      nlinarith
    rw [hedge]
    have hsq : (4 * (m : ℝ) - n) ^ 2 ≤ ((4 - 2 * s) * m) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hid : ((4 - 2 * s) * (m : ℝ)) ^ 2 = 4 * m * ((7 - 4 * s) * m) := by
      linear_combination 4 * (m : ℝ) ^ 2 * hs
    have hedgeR : (4 * (m : ℝ) - n) ^ 2 < 4 * m * r :=
      (hsq.trans_eq hid).trans_lt (mul_lt_mul_of_pos_left hrl (by positivity))
    exact_mod_cast (show (n : ℝ) ^ 2 < 4 * (2 * m * a + m * r) by rw [ha'] at hedgeR ⊢; nlinarith)
  · obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.1 ht
    have hxy' := iso.map_adj_iff.2 hxy; have hxz' := iso.map_adj_iff.2 hxz
    have hyz' := iso.map_adj_iff.2 hyz
    have hts : ∑ v ∈ ({x, y, z} : Finset (Fin n)), G.degree v = 2 * m + 2 * (a + r) := by
      rw [sum_insert (by simp [hxy.ne, hxz.ne]), sum_pair hyz.ne,
        ← iso.degree_eq x, ← iso.degree_eq y, ← iso.degree_eq z, hdeg, hdeg, hdeg]
      rcases hx' : iso x with x' | x' | x' <;> rcases hy' : iso y with y' | y' | y' <;>
        rcases hz' : iso z with z' | z' | z' <;>
        (try rw [hx'] at hxy' hxz') <;> (try rw [hy'] at hxy' hyz') <;> (try rw [hz'] at hxz' hyz') <;>
        dsimp [H, adj] at hxy' hxz' hyz' ⊢ <;>
        first | exact False.elim hxy' | exact False.elim hxz' | exact False.elim hyz' | omega
    rw [← Nat.cast_sum, hts]; push_cast
    have hgap : (4 - 2 * s) * ((n : ℝ) - 2 * s * m) ≤ 4 := by
      have hn0 : 0 ≤ (n : ℝ) - 2 * s * m := by linarith only [hmlo]
      have hδ : (n : ℝ) - 2 * s * m ≤ 4 := by linarith only [hmhi, hsU]
      nlinarith only [hn0, hδ, hsL, hsU, mul_nonneg hn0 (show 0 ≤ 2 * s - 3 by linarith only [hsL])]
    have hgap' : 4 * (n : ℝ) - 8 * s * m - 2 * s * n + 12 * m ≤ 4 := by
      linear_combination hgap - 4 * (m : ℝ) * hs
    change 2 * (m : ℝ) + 2 * (a + (r : ℝ)) ≤ 2 * (s - 1) * n + 6
    linarith only [ha', hru, hgap']
