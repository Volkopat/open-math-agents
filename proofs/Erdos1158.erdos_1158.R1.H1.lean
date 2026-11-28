import OMAReductions.R_Erdos1158_erdos_1158_R1
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Ring

/-!
The affine incidence graph over a prime field has one edge for each choice
of nonvertical line and first coordinate. Two distinct points determine at
most one common line, so it is four-cycle-free. Bertrand's postulate gives
a field of the required size, and the exponent loss absorbs the constant.
-/

namespace OMA.Erdos1158Incidence

open Finset

private abbrev Vertex (F : Type*) := (F × F) ⊕ (F × F)

variable {F W : Type*} [Field F]

section

variable [DecidableEq W]

private def edge (e : Vertex F ↪ W) (t : F × (F × F)) : Finset W :=
  {e (Sum.inl (t.1, t.2.1 * t.1 + t.2.2)), e (Sum.inr t.2)}

private def edges [Fintype F] (e : Vertex F ↪ W) : Finset (Finset W) := univ.image (edge e)

private theorem edge_injective (e : Vertex F ↪ W) : Function.Injective (edge e) := by
  intro t u h
  have hl : e (Sum.inr t.2) ∈ edge e u := h ▸ (by simp [edge])
  have hp : e (Sum.inl (t.1, t.2.1 * t.1 + t.2.2)) ∈ edge e u := h ▸ (by simp [edge])
  simp only [edge, mem_insert, mem_singleton, e.injective.eq_iff, Sum.inr_ne_inl,
    Sum.inl_ne_inr, Sum.inl.injEq, Sum.inr.injEq, false_or, or_false] at hl hp
  exact Prod.ext (congrArg (fun p : F × F => p.1) hp) hl

private theorem card_edges [Fintype F] (e : Vertex F ↪ W) :
    (edges e).card = (Fintype.card F)^3 := by
  rw [edges, card_image_of_injective _ (edge_injective e)]
  simp [pow_succ, mul_assoc]

private theorem edges_uniform [Fintype F] (e : Vertex F ↪ W) : (edges e).IsUniform 2 := by
  intro s hs
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
  exact Finset.card_pair (fun he => Sum.inl_ne_inr (e.injective he))

end

private def incident (e : Vertex F ↪ W) (u v : W) : Prop :=
  (∃ P L : F × F, u = e (Sum.inl P) ∧ v = e (Sum.inr L) ∧ P.2 = L.1 * P.1 + L.2) ∨
  (∃ P L : F × F, v = e (Sum.inl P) ∧ u = e (Sum.inr L) ∧ P.2 = L.1 * P.1 + L.2)

private theorem incident_swap (e : Vertex F ↪ W) {u v : W} :
    incident e u v → incident e v u := Or.symm

private theorem incident_of_pair_mem [Fintype F] [DecidableEq W] (e : Vertex F ↪ W) {u v : W}
    (hne : u ≠ v) (h : ({u,v} : Finset W) ∈ edges e) : incident e u v := by
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
  have hu : u ∈ edge e t := by rw [ht]; simp
  have hv : v ∈ edge e t := by rw [ht]; simp
  simp only [edge, mem_insert, mem_singleton] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact (hne (hu.trans hv.symm)).elim
  · exact Or.inl ⟨_, _, hu, hv, rfl⟩
  · exact Or.inr ⟨_, _, hv, hu, rfl⟩
  · exact (hne (hu.trans hv.symm)).elim

private theorem line_of_point (e : Vertex F ↪ W) (P : F × F) {v : W}
    (h : incident e (e (Sum.inl P)) v) :
    ∃ L : F × F, v = e (Sum.inr L) ∧ P.2 = L.1 * P.1 + L.2 := by
  rcases h with ⟨P', L, hp, hv, hPL⟩ | ⟨_, _, _, hp, _⟩
  · have hp' : P = P' := Sum.inl.inj (e.injective hp)
    exact ⟨L, hv, hp'.symm ▸ hPL⟩
  · exact (Sum.inl_ne_inr (e.injective hp)).elim

private theorem point_of_line (e : Vertex F ↪ W) (L : F × F) {u : W}
    (h : incident e u (e (Sum.inr L))) :
    ∃ P : F × F, u = e (Sum.inl P) ∧ P.2 = L.1 * P.1 + L.2 := by
  rcases h with ⟨P, L', hp, hL, hPL⟩ | ⟨_, _, hL, _, _⟩
  · have hl' : L = L' := Sum.inr.inj (e.injective hL)
    exact ⟨P, hp, hl'.symm ▸ hPL⟩
  · exact (Sum.inr_ne_inl (e.injective hL)).elim

private theorem line_eq_of_two_points {P Q L M : F × F} (hPQ : P ≠ Q)
    (hpL : P.2 = L.1 * P.1 + L.2) (hqL : Q.2 = L.1 * Q.1 + L.2)
    (hpM : P.2 = M.1 * P.1 + M.2) (hqM : Q.2 = M.1 * Q.1 + M.2) : L = M := by
  have hx : P.1 ≠ Q.1 := fun he => hPQ (Prod.ext he (by rw [hpL, hqL, he]))
  have hdiff (A : F × F) (hp : P.2 = A.1 * P.1 + A.2) (hq : Q.2 = A.1 * Q.1 + A.2) :
      P.2 - Q.2 = A.1 * (P.1 - Q.1) := by
    rw [hp, hq, add_sub_add_right_eq_sub, mul_sub]
  have hs : L.1 = M.1 :=
    mul_right_cancel₀ (sub_ne_zero.mpr hx) ((hdiff L hpL hqL).symm.trans (hdiff M hpM hqM))
  have hb : L.1 * P.1 + L.2 = L.1 * P.1 + M.2 :=
    hpL.symm.trans (by simpa only [← hs] using hpM)
  exact Prod.ext hs (add_left_cancel hb)

private theorem no_oriented_rectangle (e : Vertex F ↪ W) {u u' v v' : W} {P L : F × F}
    (hu : u = e (Sum.inl P)) (hv : v = e (Sum.inr L)) (hPL : P.2 = L.1 * P.1 + L.2)
    (huu : u ≠ u') (hvv : v ≠ v') (h01 : incident e u v') (h10 : incident e u' v)
    (h11 : incident e u' v') : False := by
  obtain ⟨M, hv', hPM⟩ := line_of_point e P (hu ▸ h01)
  obtain ⟨Q, hu', hQL⟩ := point_of_line e L (hv ▸ h10)
  obtain ⟨M', hv'', hQM'⟩ := line_of_point e Q (hu' ▸ h11)
  have hM : M' = M := Sum.inr.inj (e.injective (hv''.symm.trans hv'))
  have hQM : Q.2 = M.1 * Q.1 + M.2 := hM ▸ hQM'
  have hPQ : P ≠ Q := fun h => huu (hu.trans ((congrArg (fun p => e (Sum.inl p)) h).trans hu'.symm))
  have hLM := line_eq_of_two_points hPQ hPL hQL hPM hQM
  exact hvv (hv.trans ((congrArg (fun l => e (Sum.inr l)) hLM).trans hv'.symm))

private theorem no_rectangle (e : Vertex F ↪ W) {u u' v v' : W}
    (huu : u ≠ u') (hvv : v ≠ v') (h00 : incident e u v) (h01 : incident e u v')
    (h10 : incident e u' v) (h11 : incident e u' v') : False := by
  rcases h00 with ⟨P, L, hu, hv, hPL⟩ | ⟨P, L, hv, hu, hPL⟩
  · exact no_oriented_rectangle e hu hv hPL huu hvv h01 h10 h11
  · exact no_oriented_rectangle e hv hu hPL hvv huu
      (incident_swap e h10) (incident_swap e h01) (incident_swap e h11)

private theorem edges_no_K22 [Fintype F] [DecidableEq W] (e : Vertex F ↪ W) :
    ¬ (edges e).ContainsCompletePartiteHypergraph 2 2 := by
  rintro ⟨f, hf⟩
  have unequal {a b : Fin 2 × Fin 2} (h : a ≠ b) : f a ≠ f b :=
    fun he => h (f.injective he)
  have inc (x y : Fin 2) : incident e (f (0,x)) (f (1,y)) := by
    let labels : Fin 2 → Fin 2 := fun i => if i = 0 then x else y
    have hp : univ.image (fun i => f (i, labels i)) = {f (0,x), f (1,y)} := by
      ext u
      simp [Fin.exists_fin_two, labels, eq_comm]
    have hn : ((0,x) : Fin 2 × Fin 2) ≠ (1,y) :=
      fun he => (show (0 : Fin 2) ≠ 1 by decide) (congrArg Prod.fst he)
    exact incident_of_pair_mem e (unequal hn) (hp ▸ hf labels)
  have hL : ((0,0) : Fin 2 × Fin 2) ≠ (0,1) := by decide
  have hR : ((1,0) : Fin 2 × Fin 2) ≠ (1,1) := by decide
  exact no_rectangle e (unequal hL) (unequal hR) (inc 0 0) (inc 0 1) (inc 1 0) (inc 1 1)

/-- A finite prime field supplies a four-cycle-free graph with `p^3` edges. -/
theorem prime_cube_le_partite_extremal {p n : ℕ} (hp : p.Prime) (hsize : 2 * p^2 ≤ n) :
    p^3 ≤ Hypergraph.partiteExtremalNumber n 2 2 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Fintype.card (Vertex (ZMod p)) ≤ Fintype.card (Fin n) := by
    simpa [pow_two, two_mul, Vertex, ZMod.card] using hsize
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  rw [Hypergraph.partiteExtremalNumber, Hypergraph.extremalNumber, ← ZMod.card p, ← card_edges e]
  apply Finset.le_sup
  simp only [Finset.mem_filter]
  refine ⟨Finset.mem_powerset.mpr ?_, edges_no_K22 e⟩
  intro E hE
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ E, edges_uniform e E hE⟩

end OMA.Erdos1158Incidence

namespace OMA.Erdos1158Incidence

open Filter

private theorem three_halves_of_square (x : ℝ) (hx : 0 ≤ x) :
    (x ^ 2) ^ (3 / 2 : ℝ) = x ^ 3 := by
  calc
    _ = x ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
      norm_num
    _ = _ := Real.rpow_natCast x 3

theorem eventually_prime_cube_bound {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ 2 * p ^ 2 ≤ n ∧
      (n : ℝ) ^ (3 / 2 - ε) ≤ (p : ℝ) ^ 3 := by
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (8 : ℕ), htend.eventually_ge_atTop (64 : ℝ)]
    with n hn hlarge
  let m := Nat.sqrt (n / 8)
  have hm : 0 < m := Nat.sqrt_pos.mpr (by omega)
  obtain ⟨p, hp, hmp, hpm⟩ := Nat.exists_prime_lt_and_le_two_mul m hm.ne'
  have hmsq : m ^ 2 ≤ n / 8 := by simpa only [pow_two] using Nat.sqrt_le (n / 8)
  have hsmall : 2 * p ^ 2 ≤ n := by
    calc
      _ ≤ 2 * (2 * m) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpm 2)
      _ = 8 * m ^ 2 := by ring
      _ ≤ 8 * (n / 8) := Nat.mul_le_mul_left _ hmsq
      _ ≤ n := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self n 8
  have hsq : n / 8 < p ^ 2 := Nat.sqrt_lt'.mp hmp
  have hbig : n ≤ 16 * p ^ 2 := by
    have h := (Nat.div_lt_iff_lt_mul (by decide : 0 < 8)).mp hsq
    omega
  have hbigR : (n : ℝ) ≤ (4 * (p : ℝ)) ^ 2 := by
    calc
      _ ≤ 16 * (p : ℝ) ^ 2 := by exact_mod_cast hbig
      _ = _ := by ring
  have hpow : (n : ℝ) ^ (3 / 2 : ℝ) ≤ 64 * (p : ℝ) ^ 3 := by
    calc
      _ ≤ ((4 * (p : ℝ)) ^ 2) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hbigR (by norm_num)
      _ = (4 * (p : ℝ)) ^ 3 := three_halves_of_square _ (by positivity)
      _ = _ := by ring
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  refine ⟨p, hp, hsmall, ?_⟩
  rw [Real.rpow_sub hnpos]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hnpos _)).mpr
  exact hpow.trans (by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ (p : ℝ) ^ 3))

end OMA.Erdos1158Incidence

open Filter OMA.Erdos1158Incidence in
theorem OMA.solution : OMA.R_Erdos1158_erdos_1158_R1.H1 := by
  intro ε hε
  have hex : (2 : ℝ) - (2 : ℝ) ^ (1 - (2 : ℝ)) - ε = 3 / 2 - ε := by
    rw [show 1 - (2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    ring
  change ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (2 - (2 : ℝ) ^ (1 - (2 : ℝ)) - ε) ≤
      (Hypergraph.partiteExtremalNumber n 2 2 : ℝ)
  rw [hex]
  filter_upwards [eventually_prime_cube_bound hε] with n hn
  obtain ⟨p, hp, hsize, hbound⟩ := hn
  exact hbound.trans (by exact_mod_cast prime_cube_le_partite_extremal hp hsize)
