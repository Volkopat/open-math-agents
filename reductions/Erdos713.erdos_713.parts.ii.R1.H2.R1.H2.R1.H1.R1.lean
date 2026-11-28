import OMAReductions.R_Erdos713_erdos_713_parts_ii_R1_H2_R1_H2_R1

/-!
# Reduction Erdos713.erdos_713.parts.ii.R1.H2.R1.H2.R1.H1.R1

Splits the rational-exponent range `α ∈ (1, 3/2)` of Erdős Problem 713(ii) cleanly at `α = 4/3`:

1. **Lower bound (`E713Wenger`)**: For every prime `p`, Wenger's bipartite graph `W₃(p)` on
   `(ZMod p)³ ⊕ (ZMod p)³` (`p ~ l ↔ l₂ + p₂ = l₁ p₁ ∧ l₃ + p₃ = l₁ p₂`) is `C₆`-free (proved
   directly via the 3×3 Vandermonde system along any putative 6-cycle), has `2 p³` vertices, and
   is `p`-regular with `p⁴` edges. Bertrand's postulate on `⌊(n / 2)^(1/3)⌋` and
   `E713Amplify.padding` give `n^(4/3) = O(extremalNumber n F)` whenever `cycleGraph 6 ⊑ F`.
2. **Upper bound (`E713BondySimonovits`)**: Complete elementary proof of Bondy–Simonovits for `C₆`,
   `extremalNumber n (cycleGraph 6) = O(n^(4/3))`:
   - Max-cut bipartite subgraph retaining at least half the edges (`exists_bipartite_sub`).
   - High-minimum-degree core extraction (`exists_min_deg_sub`).
   - Bipartite `P₅`-free edge bound `|E(A, B)| ≤ 2 |B| + |A|` (`no_P5_bipartite_edges`).
   - Depth-3 BFS layer expansion in a `C₆`-free bipartite graph yielding
     `(d - 4) (d - 2) d ≤ 4 n` (`c6_free_bipartite_min_deg`).
3. **Exact `Θ(n^(4/3))` and split at `4/3`**: Proves `ex(n, C₆) = Θ(n^(4/3))`, rules out `α < 4/3`
   when `cycleGraph 6 ⊑ G` and rules out `α > 4/3` when `G ⊑ cycleGraph 6`; at `α = 4/3` the
   exponent is rational.

References:
- R. Wenger, Extremal graphs with no `C⁴`'s, `C⁶`'s, or `C¹⁰`'s, J. Combin. Theory Ser. B 52
  (1991), 113–116.
- J. A. Bondy and M. Simonovits, Cycles of even length in graphs, J. Combin. Theory Ser. B 16
  (1974), 97–105.
-/

-- Credit: @sanchan

section

open SimpleGraph Finset
open scoped Classical

namespace E713Wenger

lemma wenger_c6_contra {K : Type*} [Field K]
    (p0 p1 p2 l0 l1 l2 : K × K × K)
    (hp01 : p0 ≠ p1) (hl01 : l0 ≠ l1) (hl12 : l1 ≠ l2) (hl20 : l2 ≠ l0)
    (h00 : l0.2.1 + p0.2.1 = l0.1 * p0.1 ∧ l0.2.2 + p0.2.2 = l0.1 * p0.2.1)
    (h10 : l0.2.1 + p1.2.1 = l0.1 * p1.1 ∧ l0.2.2 + p1.2.2 = l0.1 * p1.2.1)
    (h11 : l1.2.1 + p1.2.1 = l1.1 * p1.1 ∧ l1.2.2 + p1.2.2 = l1.1 * p1.2.1)
    (h21 : l1.2.1 + p2.2.1 = l1.1 * p2.1 ∧ l1.2.2 + p2.2.2 = l1.1 * p2.2.1)
    (h22 : l2.2.1 + p2.2.1 = l2.1 * p2.1 ∧ l2.2.2 + p2.2.2 = l2.1 * p2.2.1)
    (h02 : l2.2.1 + p0.2.1 = l2.1 * p0.1 ∧ l2.2.2 + p0.2.2 = l2.1 * p0.2.1) : False := by
  have hab : l0.1 ≠ l1.1 := by
    intro h
    apply hl01
    rw [h] at h10
    refine Prod.ext h (Prod.ext ?_ ?_)
    · linear_combination h10.1 - h11.1
    · linear_combination h10.2 - h11.2
  have hbc : l1.1 ≠ l2.1 := by
    intro h
    apply hl12
    rw [h] at h21
    refine Prod.ext h (Prod.ext ?_ ?_)
    · linear_combination h21.1 - h22.1
    · linear_combination h21.2 - h22.2
  have hca : l2.1 ≠ l0.1 := by
    intro h
    apply hl20
    rw [h] at h02
    refine Prod.ext h (Prod.ext ?_ ?_)
    · linear_combination h02.1 - h00.1
    · linear_combination h02.2 - h00.2
  have dy1 : p1.2.1 - p0.2.1 = l0.1 * (p1.1 - p0.1) := by linear_combination h10.1 - h00.1
  have dy2 : p2.2.1 - p1.2.1 = l1.1 * (p2.1 - p1.1) := by linear_combination h21.1 - h11.1
  have dy3 : p0.2.1 - p2.2.1 = l2.1 * (p0.1 - p2.1) := by linear_combination h02.1 - h22.1
  have dz1 : p1.2.2 - p0.2.2 = l0.1 * (p1.2.1 - p0.2.1) := by linear_combination h10.2 - h00.2
  have dz2 : p2.2.2 - p1.2.2 = l1.1 * (p2.2.1 - p1.2.1) := by linear_combination h21.2 - h11.2
  have dz3 : p0.2.2 - p2.2.2 = l2.1 * (p0.2.1 - p2.2.1) := by linear_combination h02.2 - h22.2
  have hvan : (l0.1 - l1.1) * (l0.1 - l2.1) * (p1.1 - p0.1) = 0 := by
    linear_combination
      (l1.1 + l2.1) * (dy1 + dy2 + dy3) -
      (dz1 + dz2 + dz3 + l0.1 * dy1 + l1.1 * dy2 + l2.1 * dy3)
  have hdx : p1.1 - p0.1 = 0 :=
    (mul_eq_zero.mp hvan).resolve_left (mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hca.symm))
  have hx : p1.1 = p0.1 := sub_eq_zero.mp hdx
  rw [hdx, mul_zero] at dy1
  have hy : p1.2.1 = p0.2.1 := sub_eq_zero.mp dy1
  rw [dy1, mul_zero] at dz1
  have hz : p1.2.2 = p0.2.2 := sub_eq_zero.mp dz1
  exact hp01 (Prod.ext hx.symm (Prod.ext hy.symm hz.symm))

/-- Wenger's bipartite graph `W₃(p)` is `C₆`-free and has at least `p⁴` edges on `2 p³` vertices. -/
theorem wenger_witness (p : ℕ) [Fact p.Prime] :
    ∃ G : SimpleGraph ((ZMod p × ZMod p × ZMod p) ⊕ (ZMod p × ZMod p × ZMod p)),
      (cycleGraph 6).Free G ∧ p ^ 4 ≤ G.edgeFinset.card := by
  let K := ZMod p
  let R : (K × K × K) → (K × K × K) → Prop := fun pt ln =>
    ln.2.1 + pt.2.1 = ln.1 * pt.1 ∧ ln.2.2 + pt.2.2 = ln.1 * pt.2.1
  let G : SimpleGraph ((K × K × K) ⊕ (K × K × K)) := {
    Adj u v := match u, v with
      | Sum.inl pt, Sum.inr ln => R pt ln
      | Sum.inr ln, Sum.inl pt => R pt ln
      | _, _ => False
    symm := ⟨fun u v h => by cases u <;> cases v <;> exact h⟩
    loopless := ⟨fun u h => by cases u <;> exact h⟩ }
  refine ⟨G, ?_, ?_⟩
  · rintro ⟨e⟩
    have hedge : ∀ i : Fin 6, G.Adj (e i) (e (i + 1)) := fun i =>
      e.toHom.map_rel' (by fin_cases i <;> decide)
    have h01 : G.Adj (e 0) (e 1) := hedge 0
    have h12 : G.Adj (e 1) (e 2) := hedge 1
    have h23 : G.Adj (e 2) (e 3) := hedge 2
    have h34 : G.Adj (e 3) (e 4) := hedge 3
    have h45 : G.Adj (e 4) (e 5) := hedge 4
    have h50 : G.Adj (e 5) (e 0) := hedge 5
    have hne : ∀ i j : Fin 6, i ≠ j → e i ≠ e j := fun i j h => e.injective.ne h
    cases hv0 : e 0 with
    | inl p0 =>
      rw [hv0] at h01 h50
      cases hv1 : e 1 with
      | inl _ => rw [hv1] at h01; exact h01
      | inr l0 =>
        rw [hv1] at h01 h12
        cases hv2 : e 2 with
        | inr _ => rw [hv2] at h12; exact h12
        | inl p1 =>
          rw [hv2] at h12 h23
          cases hv3 : e 3 with
          | inl _ => rw [hv3] at h23; exact h23
          | inr l1 =>
            rw [hv3] at h23 h34
            cases hv4 : e 4 with
            | inr _ => rw [hv4] at h34; exact h34
            | inl p2 =>
              rw [hv4] at h34 h45
              cases hv5 : e 5 with
              | inl _ => rw [hv5] at h45; exact h45
              | inr l2 =>
                rw [hv5] at h45 h50
                exact wenger_c6_contra p0 p1 p2 l0 l1 l2
                  (fun h => hne 0 2 (by decide) (by rw [hv0, hv2, h]))
                  (fun h => hne 1 3 (by decide) (by rw [hv1, hv3, h]))
                  (fun h => hne 3 5 (by decide) (by rw [hv3, hv5, h]))
                  (fun h => hne 5 1 (by decide) (by rw [hv5, hv1, h]))
                  h01 h12 h23 h34 h45 h50
    | inr l2 =>
      rw [hv0] at h01 h50
      cases hv1 : e 1 with
      | inr _ => rw [hv1] at h01; exact h01
      | inl p0 =>
        rw [hv1] at h01 h12
        cases hv2 : e 2 with
        | inl _ => rw [hv2] at h12; exact h12
        | inr l0 =>
          rw [hv2] at h12 h23
          cases hv3 : e 3 with
          | inr _ => rw [hv3] at h23; exact h23
          | inl p1 =>
            rw [hv3] at h23 h34
            cases hv4 : e 4 with
            | inl _ => rw [hv4] at h34; exact h34
            | inr l1 =>
              rw [hv4] at h34 h45
              cases hv5 : e 5 with
              | inr _ => rw [hv5] at h45; exact h45
              | inl p2 =>
                rw [hv5] at h45 h50
                exact wenger_c6_contra p0 p1 p2 l0 l1 l2
                  (fun h => hne 1 3 (by decide) (by rw [hv1, hv3, h]))
                  (fun h => hne 2 4 (by decide) (by rw [hv2, hv4, h]))
                  (fun h => hne 4 0 (by decide) (by rw [hv4, hv0, h]))
                  (fun h => hne 0 2 (by decide) (by rw [hv0, hv2, h]))
                  h12 h23 h34 h45 h50 h01
  · have hdeg : ∀ u : (K × K × K) ⊕ (K × K × K), p ≤ G.degree u := by
      intro u
      cases u with
      | inl pt =>
        let φ : K → (K × K × K) ⊕ (K × K × K) := fun x =>
          Sum.inr (x, x * pt.1 - pt.2.1, x * pt.2.1 - pt.2.2)
        have hinj : Function.Injective φ := fun x y h =>
          congrArg Prod.fst (Sum.inr.inj h)
        have hsub : (Finset.univ : Finset K).image φ ⊆ G.neighborFinset (Sum.inl pt) := by
          intro w hw
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hw
          rw [G.mem_neighborFinset]
          exact ⟨by ring, by ring⟩
        calc p = (Finset.univ : Finset K).card := by rw [Finset.card_univ, ZMod.card p]
          _ = ((Finset.univ : Finset K).image φ).card := (Finset.card_image_of_injective _ hinj).symm
          _ ≤ (G.neighborFinset (Sum.inl pt)).card := Finset.card_le_card hsub
          _ = G.degree (Sum.inl pt) := G.card_neighborFinset_eq_degree _
      | inr ln =>
        let ψ : K → (K × K × K) ⊕ (K × K × K) := fun x =>
          Sum.inl (x, ln.1 * x - ln.2.1, ln.1 * (ln.1 * x - ln.2.1) - ln.2.2)
        have hinj : Function.Injective ψ := fun x y h =>
          congrArg Prod.fst (Sum.inl.inj h)
        have hsub : (Finset.univ : Finset K).image ψ ⊆ G.neighborFinset (Sum.inr ln) := by
          intro w hw
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hw
          rw [G.mem_neighborFinset]
          exact ⟨by ring, by ring⟩
        calc p = (Finset.univ : Finset K).card := by rw [Finset.card_univ, ZMod.card p]
          _ = ((Finset.univ : Finset K).image ψ).card := (Finset.card_image_of_injective _ hinj).symm
          _ ≤ (G.neighborFinset (Sum.inr ln)).card := Finset.card_le_card hsub
          _ = G.degree (Sum.inr ln) := G.card_neighborFinset_eq_degree _
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hdeg u)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_prod,
        ZMod.card p, smul_eq_mul, G.sum_degrees_eq_twice_card_edges] at hsum
    have hlhs : (p * (p * p) + p * (p * p)) * p = 2 * p ^ 4 := by ring
    rw [hlhs] at hsum
    have hfin : 2 * p ^ 4 ≤ 2 * G.edgeFinset.card := by
      convert! hsum using 2
    omega

lemma c6_no_isolated : ∀ v : Fin 6, ¬ (cycleGraph 6).IsIsolated v := by
  intro v h
  exact h (v + 1) (by fin_cases v <;> decide)

/-- Uniform lower bound `n⁴ ≤ 64³ * ex(n, C₆)³` for `n ≥ 54` via Bertrand's postulate. -/
theorem c6_lower_uniform (n : ℕ) (hn : 54 ≤ n) :
    n ^ 4 ≤ 64 ^ 3 * (extremalNumber n (cycleGraph 6)) ^ 3 := by
  let S := (Finset.range (n + 1)).filter (fun m => 2 * m ^ 3 ≤ n)
  have h0S : 0 ∈ S := by simp [S]
  let k := S.max' ⟨0, h0S⟩
  have hk_mem : k ∈ S := Finset.max'_mem S ⟨0, h0S⟩
  have hk3_le : 2 * k ^ 3 ≤ n := (Finset.mem_filter.mp hk_mem).2
  have h3_mem : 3 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩
  have hk3 : 3 ≤ k := Finset.le_max' S 3 h3_mem
  have hlt_succ : n < 2 * (k + 1) ^ 3 := by
    by_contra hle
    push Not at hle
    have hk1_le : k + 1 ≤ n := by
      have : k + 1 ≤ (k + 1) ^ 3 := Nat.le_self_pow (by omega) _
      omega
    have hk1_mem : k + 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hle⟩
    have := Finset.le_max' S (k + 1) hk1_mem
    omega
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (k / 2) (by omega)
  have hpk : p ≤ k := by omega
  have hk_2p : k + 1 ≤ 2 * p := by omega
  have hp3_le_n : 2 * p ^ 3 ≤ n := (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hpk 3)).trans hk3_le
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨G, hfree, hedges⟩ := wenger_witness p
  have hcardW : Fintype.card ((ZMod p × ZMod p × ZMod p) ⊕ (ZMod p × ZMod p × ZMod p)) = 2 * p ^ 3 := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, ZMod.card p]; ring
  have hpad : G.edgeFinset.card ≤ extremalNumber n (cycleGraph 6) :=
    E713Amplify.padding (cycleGraph 6) c6_no_isolated G hfree n (hcardW.le.trans hp3_le_n)
  have hp4_le : p ^ 4 ≤ extremalNumber n (cycleGraph 6) := hedges.trans hpad
  have hn_le : n ≤ 16 * p ^ 3 := by
    have h1 : (k + 1) ^ 3 ≤ (2 * p) ^ 3 := Nat.pow_le_pow_left hk_2p 3
    have h2 : (2 * p) ^ 3 = 8 * p ^ 3 := by ring
    omega
  have hn4 : n ^ 4 ≤ (16 * p ^ 3) ^ 4 := Nat.pow_le_pow_left hn_le 4
  have hp12 : (p ^ 4) ^ 3 ≤ (extremalNumber n (cycleGraph 6)) ^ 3 := Nat.pow_le_pow_left hp4_le 3
  have hid1 : (16 * p ^ 3) ^ 4 = 65536 * (p ^ 4) ^ 3 := by ring
  calc n ^ 4 ≤ (16 * p ^ 3) ^ 4 := hn4
    _ = 65536 * (p ^ 4) ^ 3 := hid1
    _ ≤ 65536 * (extremalNumber n (cycleGraph 6)) ^ 3 := Nat.mul_le_mul_left _ hp12
    _ ≤ 64 ^ 3 * (extremalNumber n (cycleGraph 6)) ^ 3 := Nat.mul_le_mul_right _ (by decide)

end E713Wenger

end

section

open SimpleGraph Finset
open scoped Classical

namespace E713BondySimonovits

/-- Every finite graph contains a bipartite spanning subgraph with at least half the edges. -/
theorem exists_bipartite_sub {W : Type*} [Fintype W] (X : SimpleGraph W) :
    ∃ (S : Finset W) (H : SimpleGraph W), H ≤ X ∧
      (∀ u v, H.Adj u v → (u ∈ S ↔ v ∉ S)) ∧
      X.edgeFinset.card ≤ 2 * H.edgeFinset.card := by
  let cutVal : Finset W → ℕ := fun S =>
    ∑ u : W, ((X.neighborFinset u).filter (fun w => u ∈ S ↔ w ∉ S)).card
  obtain ⟨S, _, hSmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset W)) cutVal
    ⟨∅, Finset.mem_univ _⟩
  let H : SimpleGraph W := {
    Adj u v := X.Adj u v ∧ (u ∈ S ↔ v ∉ S)
    symm := ⟨fun u v h => ⟨h.1.symm, by tauto⟩⟩
    loopless := ⟨fun u h => X.loopless.irrefl u h.1⟩ }
  refine ⟨S, H, fun _ _ h => h.1, fun _ _ h => h.2, ?_⟩
  have hdeg : ∀ v : W, X.degree v ≤ 2 * H.degree v := by
    intro v
    obtain ⟨S', hmemS'_v, hmemS'_ne⟩ :
        ∃ S' : Finset W, (v ∈ S' ↔ v ∉ S) ∧ ∀ x : W, x ≠ v → (x ∈ S' ↔ x ∈ S) := by
      by_cases hv : v ∈ S
      · refine ⟨S.erase v, by simp [hv], fun x hx => by simp [hx]⟩
      · refine ⟨insert v S, by simp [hv], fun x hx => by simp [hx]⟩
    have hle : cutVal S' ≤ cutVal S := hSmax S' (Finset.mem_univ _)
    have hiff_flip : ∀ u : W, u ≠ v → ((u ∈ S' ↔ v ∉ S') ↔ ¬ (u ∈ S ↔ v ∉ S)) := by
      intro u huv
      rw [hmemS'_ne u huv, hmemS'_v]
      by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]
    have hiff_flip_v : ∀ w : W, w ≠ v → ((v ∈ S' ↔ w ∉ S') ↔ ¬ (v ∈ S ↔ w ∉ S)) := by
      intro w hwv
      rw [hmemS'_v, hmemS'_ne w hwv]
      by_cases hv : v ∈ S <;> by_cases hw : w ∈ S <;> simp [hv, hw]
    let diffV := (X.neighborFinset v).filter (fun w => v ∈ S ↔ w ∉ S)
    let sameV := (X.neighborFinset v).filter (fun w => ¬ (v ∈ S ↔ w ∉ S))
    have hdiff_eq : diffV.card = H.degree v := by
      rw [← H.card_neighborFinset_eq_degree v]
      congr 1; ext w; simp [diffV, SimpleGraph.mem_neighborFinset, H]
    have hsum_v : diffV.card + sameV.card = X.degree v := by
      rw [← X.card_neighborFinset_eq_degree v]
      exact Finset.card_filter_add_card_filter_not _
    have hv_term : ((X.neighborFinset v).filter (fun w => v ∈ S' ↔ w ∉ S')).card = sameV.card := by
      congr 1; ext w
      simp only [sameV, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_congr_right fun hadj => hiff_flip_v w hadj.ne.symm
    have hother : ∀ u ∈ (Finset.univ : Finset W).erase v,
        ((X.neighborFinset u).filter (fun w => u ∈ S' ↔ w ∉ S')).card +
          (if X.Adj u v ∧ (u ∈ S ↔ v ∉ S) then 1 else 0) =
        ((X.neighborFinset u).filter (fun w => u ∈ S ↔ w ∉ S)).card +
          (if X.Adj u v ∧ ¬ (u ∈ S ↔ v ∉ S) then 1 else 0) := by
      intro u hu
      have huv : u ≠ v := (Finset.mem_erase.mp hu).1
      set F1 := (X.neighborFinset u).filter (fun w => u ∈ S' ↔ w ∉ S')
      set F0 := (X.neighborFinset u).filter (fun w => u ∈ S ↔ w ∉ S)
      have herase : F1.erase v = F0.erase v := by
        ext w
        simp only [F1, F0, Finset.mem_erase, Finset.mem_filter]
        exact and_congr_right fun hwv => and_congr_right fun _ => by
          rw [hmemS'_ne u huv, hmemS'_ne w hwv]
      have hcard1 : F1.card = (F1.erase v).card + if v ∈ F1 then 1 else 0 := by
        by_cases h : v ∈ F1
        · rw [if_pos h, Finset.card_erase_add_one h]
        · rw [if_neg h, add_zero, Finset.erase_eq_of_notMem h]
      have hcard0 : F0.card = (F0.erase v).card + if v ∈ F0 then 1 else 0 := by
        by_cases h : v ∈ F0
        · rw [if_pos h, Finset.card_erase_add_one h]
        · rw [if_neg h, add_zero, Finset.erase_eq_of_notMem h]
      have hm1 : v ∈ F1 ↔ X.Adj u v ∧ ¬ (u ∈ S ↔ v ∉ S) := by
        simp only [F1, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
        exact and_congr_right fun _ => hiff_flip u huv
      have hm0 : v ∈ F0 ↔ X.Adj u v ∧ (u ∈ S ↔ v ∉ S) := by
        simp only [F0, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      have hite1 : (if v ∈ F1 then 1 else 0) = if X.Adj u v ∧ ¬ (u ∈ S ↔ v ∉ S) then 1 else 0 :=
        if_congr hm1 rfl rfl
      have hite0 : (if v ∈ F0 then 1 else 0) = if X.Adj u v ∧ (u ∈ S ↔ v ∉ S) then 1 else 0 :=
        if_congr hm0 rfl rfl
      rw [← hite0, ← hite1, hcard1, hcard0, herase, add_right_comm]
    have hsum_other := Finset.sum_congr rfl hother
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_other
    have hcnt_diff : (∑ u ∈ (Finset.univ : Finset W).erase v,
        if X.Adj u v ∧ (u ∈ S ↔ v ∉ S) then 1 else 0) = diffV.card := by
      rw [← Finset.card_filter]
      congr 1; ext u
      simp only [diffV, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨_, hadj, hiff⟩
        exact ⟨hadj.symm, by by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp_all⟩
      · rintro ⟨hadj, hiff⟩
        exact ⟨hadj.ne.symm, hadj.symm, by by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp_all⟩
    have hcnt_same : (∑ u ∈ (Finset.univ : Finset W).erase v,
        if X.Adj u v ∧ ¬ (u ∈ S ↔ v ∉ S) then 1 else 0) = sameV.card := by
      rw [← Finset.card_filter]
      congr 1; ext u
      simp only [sameV, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨_, hadj, hiff⟩
        exact ⟨hadj.symm, by by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp_all⟩
      · rintro ⟨hadj, hiff⟩
        exact ⟨hadj.ne.symm, hadj.symm, by by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp_all⟩
    rw [hcnt_diff, hcnt_same] at hsum_other
    have hcutS' : cutVal S' = sameV.card +
        ∑ u ∈ (Finset.univ : Finset W).erase v,
          ((X.neighborFinset u).filter (fun w => u ∈ S' ↔ w ∉ S')).card := by
      dsimp only [cutVal]
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v), hv_term]
    have hcutS : cutVal S = diffV.card +
        ∑ u ∈ (Finset.univ : Finset W).erase v,
          ((X.neighborFinset u).filter (fun w => u ∈ S ↔ w ∉ S)).card := by
      dsimp only [cutVal]
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v)]
    omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hdeg v)
  rw [← Finset.mul_sum, X.sum_degrees_eq_twice_card_edges, H.sum_degrees_eq_twice_card_edges] at hsum
  convert! Nat.le_of_mul_le_mul_left hsum (by decide : 0 < 2)

/-- Every graph with `d * |W| < |E(H)|` has a nonempty induced subgraph of minimum degree `≥ d + 1`. -/
theorem exists_min_deg_sub {W : Type*} [Fintype W] (H : SimpleGraph W) (d : ℕ)
    (hE : d * Fintype.card W < H.edgeFinset.card) :
    ∃ U : Finset W, U.Nonempty ∧ ∀ u ∈ U, d + 1 ≤ (U.filter (H.Adj u)).card := by
  have go : ∀ m : ℕ, ∀ U : Finset W, U.card = m →
      2 * d * U.card < ∑ u ∈ U, (U.filter (H.Adj u)).card →
      ∃ U' : Finset W, U'.Nonempty ∧ ∀ u ∈ U', d + 1 ≤ (U'.filter (H.Adj u)).card := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro U hcard hsum
      by_cases hall : ∀ u ∈ U, d + 1 ≤ (U.filter (H.Adj u)).card
      · have hne : U.Nonempty := by
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty.mp hemp] at hsum
          simp at hsum
        exact ⟨U, hne, hall⟩
      push Not at hall
      obtain ⟨u₀, hu₀, hdu₀⟩ := hall
      let U₁ := U.erase u₀
      have hcard1 : U₁.card + 1 = U.card := Finset.card_erase_add_one hu₀
      have hsum_drop : ∑ u ∈ U, (U.filter (H.Adj u)).card =
          (∑ u ∈ U₁, (U₁.filter (H.Adj u)).card) + 2 * (U.filter (H.Adj u₀)).card := by
        rw [← Finset.add_sum_erase U _ hu₀]
        have hper : ∀ u ∈ U₁, (U.filter (H.Adj u)).card =
            (U₁.filter (H.Adj u)).card + (if H.Adj u u₀ then 1 else 0) := by
          intro u _
          by_cases hadj : H.Adj u u₀
          · rw [if_pos hadj]
            have hmem : u₀ ∈ U.filter (H.Adj u) := Finset.mem_filter.mpr ⟨hu₀, hadj⟩
            have heq : (U.filter (H.Adj u)).erase u₀ = U₁.filter (H.Adj u) := by
              ext x; simp [U₁]; tauto
            rw [← heq, Finset.card_erase_add_one hmem]
          · rw [if_neg hadj, add_zero]
            congr 1; ext x
            simp only [U₁, Finset.mem_filter, Finset.mem_erase]
            exact ⟨fun ⟨hxU, hux⟩ => ⟨⟨fun h => hadj (h ▸ hux), hxU⟩, hux⟩, fun ⟨⟨_, hxU⟩, hux⟩ => ⟨hxU, hux⟩⟩
        rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib]
        have hcnt : (∑ u ∈ U₁, if H.Adj u u₀ then 1 else 0) = (U.filter (H.Adj u₀)).card := by
          rw [← Finset.card_filter]
          congr 1; ext x
          simp only [U₁, Finset.mem_filter, Finset.mem_erase]
          exact ⟨fun ⟨⟨_, hxU⟩, hxu⟩ => ⟨hxU, hxu.symm⟩,
            fun ⟨hxU, hux⟩ => ⟨⟨hux.ne.symm, hxU⟩, hux.symm⟩⟩
        rw [hcnt]; ring
      have hsum1 : 2 * d * U₁.card < ∑ u ∈ U₁, (U₁.filter (H.Adj u)).card := by
        rw [← hcard1, mul_add, mul_one] at hsum
        omega
      exact ih U₁.card (by omega) U₁ rfl hsum1
  apply go (Fintype.card W) Finset.univ Finset.card_univ
  have htot : ∑ u : W, (Finset.univ.filter (H.Adj u)).card = 2 * H.edgeFinset.card := by
    rw [← H.sum_degrees_eq_twice_card_edges]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← H.card_neighborFinset_eq_degree u]
    congr 1; ext x; simp [SimpleGraph.mem_neighborFinset]
  rw [Finset.card_univ, htot, mul_assoc]
  omega

/-- Bipartite `P₅`-free edge bound: if no 4-edge path starts and ends in `A`, then
`|E(A, B)| ≤ 2 |B| + |A|`. -/
theorem no_P5_bipartite_edges {W : Type*} (H : SimpleGraph W) (A B : Finset W)
    (hnoP5 : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ a₃ ∈ A, ∀ b₁ ∈ B, ∀ b₂ ∈ B,
      a₁ ≠ a₂ → a₂ ≠ a₃ → a₁ ≠ a₃ → b₁ ≠ b₂ →
      H.Adj a₁ b₁ → H.Adj a₂ b₁ → H.Adj a₂ b₂ → H.Adj a₃ b₂ → False) :
    ∑ a ∈ A, (B.filter (H.Adj a)).card ≤ 2 * B.card + A.card := by
  have hdbl : ∑ a ∈ A, (B.filter (H.Adj a)).card = ∑ b ∈ B, (A.filter (H.Adj b)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    by_cases h : H.Adj a b
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  rw [hdbl]
  let Bbig := B.filter (fun b => 3 ≤ (A.filter (H.Adj b)).card)
  let Bsmall := B.filter (fun b => ¬ 3 ≤ (A.filter (H.Adj b)).card)
  have hpart : ∑ b ∈ B, (A.filter (H.Adj b)).card =
      (∑ b ∈ Bbig, (A.filter (H.Adj b)).card) + (∑ b ∈ Bsmall, (A.filter (H.Adj b)).card) :=
    (Finset.sum_filter_add_sum_filter_not B (fun b => 3 ≤ (A.filter (H.Adj b)).card) _).symm
  have hsmall : ∑ b ∈ Bsmall, (A.filter (H.Adj b)).card ≤ 2 * B.card := by
    calc ∑ b ∈ Bsmall, (A.filter (H.Adj b)).card
        ≤ ∑ _b ∈ Bsmall, 2 := Finset.sum_le_sum fun b hb => by
          have := (Finset.mem_filter.mp hb).2; omega
      _ = 2 * Bsmall.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * B.card := Nat.mul_le_mul_left 2 (Finset.card_le_card (Finset.filter_subset _ _))
  have hbig_swap : ∑ b ∈ Bbig, (A.filter (H.Adj b)).card =
      ∑ a ∈ A, (Bbig.filter (H.Adj a)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : H.Adj b a
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have hdeg1 : ∀ a ∈ A, (Bbig.filter (H.Adj a)).card ≤ 1 := by
    intro a ha
    by_contra! hgt
    obtain ⟨b₁, hb₁, b₂, hb₂, hb12⟩ := Finset.one_lt_card.mp hgt
    have hb₁B : b₁ ∈ B := (Finset.mem_filter.mp (Finset.mem_filter.mp hb₁).1).1
    have hb₂B : b₂ ∈ B := (Finset.mem_filter.mp (Finset.mem_filter.mp hb₂).1).1
    have hb₁_deg : 3 ≤ (A.filter (H.Adj b₁)).card := (Finset.mem_filter.mp (Finset.mem_filter.mp hb₁).1).2
    have hb₂_deg : 3 ≤ (A.filter (H.Adj b₂)).card := (Finset.mem_filter.mp (Finset.mem_filter.mp hb₂).1).2
    have hab₁ : H.Adj a b₁ := (Finset.mem_filter.mp hb₁).2
    have hab₂ : H.Adj a b₂ := (Finset.mem_filter.mp hb₂).2
    have h3_ne : ((A.filter (H.Adj b₂)).erase a).Nonempty := by
      rw [← Finset.card_pos]
      have := Finset.card_erase_le (s := A.filter (H.Adj b₂)) (a := a)
      have hge := Finset.pred_card_le_card_erase (s := A.filter (H.Adj b₂)) (a := a)
      omega
    obtain ⟨a₃, ha₃⟩ := h3_ne
    have ha₃_ne : a₃ ≠ a := (Finset.mem_erase.mp ha₃).1
    have ha₃A : a₃ ∈ A := (Finset.mem_filter.mp (Finset.mem_erase.mp ha₃).2).1
    have ha₃b₂ : H.Adj a₃ b₂ := ((Finset.mem_filter.mp (Finset.mem_erase.mp ha₃).2).2).symm
    have h1_ne : (((A.filter (H.Adj b₁)).erase a).erase a₃).Nonempty := by
      rw [← Finset.card_pos]
      have h1 := Finset.pred_card_le_card_erase (s := A.filter (H.Adj b₁)) (a := a)
      have h2 := Finset.pred_card_le_card_erase (s := (A.filter (H.Adj b₁)).erase a) (a := a₃)
      omega
    obtain ⟨a₁, ha₁⟩ := h1_ne
    have ha₁_ne3 : a₁ ≠ a₃ := (Finset.mem_erase.mp ha₁).1
    have ha₁_ne2 : a₁ ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp ha₁).2).1
    have ha₁A : a₁ ∈ A := (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_erase.mp ha₁).2).2).1
    have ha₁b₁ : H.Adj a₁ b₁ := ((Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_erase.mp ha₁).2).2).2).symm
    exact hnoP5 a₁ ha₁A a ha a₃ ha₃A b₁ hb₁B b₂ hb₂B ha₁_ne2 ha₃_ne.symm ha₁_ne3 hb12
      ha₁b₁ hab₁ hab₂ ha₃b₂
  have hbig : ∑ b ∈ Bbig, (A.filter (H.Adj b)).card ≤ A.card := by
    rw [hbig_swap]
    calc ∑ a ∈ A, (Bbig.filter (H.Adj a)).card
        ≤ ∑ _a ∈ A, 1 := Finset.sum_le_sum hdeg1
      _ = A.card := by simp
  omega

lemma mk_c6 {W : Type*} (H : SimpleGraph W) (x0 x1 x2 x3 x4 x5 : W)
    (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h03 : x0 ≠ x3) (h04 : x0 ≠ x4) (h05 : x0 ≠ x5)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h14 : x1 ≠ x4) (h15 : x1 ≠ x5)
    (h23 : x2 ≠ x3) (h24 : x2 ≠ x4) (h25 : x2 ≠ x5)
    (h34 : x3 ≠ x4) (h35 : x3 ≠ x5) (h45 : x4 ≠ x5)
    (e01 : H.Adj x0 x1) (e12 : H.Adj x1 x2) (e23 : H.Adj x2 x3)
    (e34 : H.Adj x3 x4) (e45 : H.Adj x4 x5) (e50 : H.Adj x5 x0) :
    cycleGraph 6 ⊑ H := by
  let f : Fin 6 → W := fun i =>
    match i.val with
    | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 4 => x4 | _ => x5
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact False.elim ((by decide : ¬ (cycleGraph 6).Adj _ _) hij)
      | exact e01 | exact e01.symm | exact e12 | exact e12.symm
      | exact e23 | exact e23.symm | exact e34 | exact e34.symm
      | exact e45 | exact e45.symm | exact e50 | exact e50.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp [f] at hij <;>
      first
      | rfl
      | exact (h01 hij).elim | exact (h01 hij.symm).elim
      | exact (h02 hij).elim | exact (h02 hij.symm).elim
      | exact (h03 hij).elim | exact (h03 hij.symm).elim
      | exact (h04 hij).elim | exact (h04 hij.symm).elim
      | exact (h05 hij).elim | exact (h05 hij.symm).elim
      | exact (h12 hij).elim | exact (h12 hij.symm).elim
      | exact (h13 hij).elim | exact (h13 hij.symm).elim
      | exact (h14 hij).elim | exact (h14 hij.symm).elim
      | exact (h15 hij).elim | exact (h15 hij.symm).elim
      | exact (h23 hij).elim | exact (h23 hij.symm).elim
      | exact (h24 hij).elim | exact (h24 hij.symm).elim
      | exact (h25 hij).elim | exact (h25 hij.symm).elim
      | exact (h34 hij).elim | exact (h34 hij.symm).elim
      | exact (h35 hij).elim | exact (h35 hij.symm).elim
      | exact (h45 hij).elim | exact (h45 hij.symm).elim

/-- Depth-3 BFS expansion in a `C₆`-free bipartite graph of minimum degree `d ≥ 5`:
`(d - 4) * (d - 2) * d ≤ 4 * |W|`. -/
theorem c6_free_bipartite_min_deg {W : Type*} [Fintype W] (H : SimpleGraph W)
    (S : Finset W) (hbip : ∀ u v, H.Adj u v → (u ∈ S ↔ v ∉ S))
    (hfree : (cycleGraph 6).Free H)
    (U : Finset W) (hne : U.Nonempty) (d : ℕ) (hd5 : 5 ≤ d)
    (hmin : ∀ u ∈ U, d ≤ (U.filter (H.Adj u)).card) :
    (d - 4) * (d - 2) * d ≤ 4 * Fintype.card W := by
  obtain ⟨v₀, hv₀⟩ := hne
  let L1 := U.filter (H.Adj v₀)
  let L2 := (U.erase v₀).filter (fun b => ∃ a ∈ L1, H.Adj a b)
  let L3 := (U \ L1).filter (fun c => ∃ b ∈ L2, H.Adj b c)
  have hL1_card : d ≤ L1.card := hmin v₀ hv₀
  have hL1_side : ∀ a ∈ L1, (a ∈ S ↔ v₀ ∉ S) := fun a ha => by
    have := hbip v₀ a (Finset.mem_filter.mp ha).2; tauto
  have hL2_side : ∀ b ∈ L2, (b ∈ S ↔ v₀ ∈ S) := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := (Finset.mem_filter.mp hb).2
    have h1 := hL1_side a ha
    have h2 := hbip a b hab
    tauto
  have hL3_side : ∀ c ∈ L3, (c ∈ S ↔ v₀ ∉ S) := by
    intro c hc
    obtain ⟨b, hb, hbc⟩ := (Finset.mem_filter.mp hc).2
    have h1 := hL2_side b hb
    have h2 := hbip b c hbc
    tauto
  have hv0_nL1 : v₀ ∉ L1 := fun h => H.loopless.irrefl v₀ (Finset.mem_filter.mp h).2
  have hv0_nL2 : v₀ ∉ L2 := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
  have hv0_nL3 : v₀ ∉ L3 := fun h => by have := hL3_side v₀ h; tauto
  have h12_disj : ∀ a ∈ L1, ∀ b ∈ L2, a ≠ b := fun a ha b hb heq => by
    have h1 := hL1_side a ha; have h2 := hL2_side b hb; rw [heq] at h1; tauto
  have h13_disj : ∀ a ∈ L1, ∀ c ∈ L3, a ≠ c := fun a ha c hc heq =>
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).1).2 (heq ▸ ha)
  have h23_disj : ∀ b ∈ L2, ∀ c ∈ L3, b ≠ c := fun b hb c hc heq => by
    have h1 := hL2_side b hb; have h2 := hL3_side c hc; rw [heq] at h1; tauto
  -- Bound E12 from above using no_P5_bipartite_edges on (L1, L2)
  have hE12_up : ∑ a ∈ L1, (L2.filter (H.Adj a)).card ≤ 2 * L2.card + L1.card := by
    apply no_P5_bipartite_edges H L1 L2
    intro a₁ ha₁ a₂ ha₂ a₃ ha₃ b₁ hb₁ b₂ hb₂ h12 h23 h13 hb12 e1 e2 e3 e4
    exact hfree (mk_c6 H v₀ a₁ b₁ a₂ b₂ a₃
      (fun h => hv0_nL1 (h ▸ ha₁)) (fun h => hv0_nL2 (h ▸ hb₁))
      (fun h => hv0_nL1 (h ▸ ha₂)) (fun h => hv0_nL2 (h ▸ hb₂))
      (fun h => hv0_nL1 (h ▸ ha₃))
      (h12_disj a₁ ha₁ b₁ hb₁) h12 (h12_disj a₁ ha₁ b₂ hb₂) h13
      (h12_disj a₂ ha₂ b₁ hb₁).symm hb12 (h12_disj a₃ ha₃ b₁ hb₁).symm
      (h12_disj a₂ ha₂ b₂ hb₂) h23 (h12_disj a₃ ha₃ b₂ hb₂).symm
      (Finset.mem_filter.mp ha₁).2 e1 e2.symm e3 e4.symm (Finset.mem_filter.mp ha₃).2.symm)
  -- Bound E12 from below: every a ∈ L1 has at least d - 1 neighbors in L2
  have hE12_lo : (d - 1) * L1.card ≤ ∑ a ∈ L1, (L2.filter (H.Adj a)).card := by
    have hper : ∀ a ∈ L1, d - 1 ≤ (L2.filter (H.Adj a)).card := by
      intro a ha
      have haU : a ∈ U := (Finset.mem_filter.mp ha).1
      have hsub : (U.filter (H.Adj a)).erase v₀ ⊆ L2.filter (H.Adj a) := by
        intro b hb
        have hne : b ≠ v₀ := (Finset.mem_erase.mp hb).1
        have hbU : b ∈ U := (Finset.mem_filter.mp (Finset.mem_erase.mp hb).2).1
        have hab : H.Adj a b := (Finset.mem_filter.mp (Finset.mem_erase.mp hb).2).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hbU⟩, ⟨a, ha, hab⟩⟩, hab⟩
      have h1 := hmin a haU
      have h2 := Finset.pred_card_le_card_erase (s := U.filter (H.Adj a)) (a := v₀)
      have h3 := Finset.card_le_card hsub
      omega
    calc (d - 1) * L1.card = ∑ _a ∈ L1, (d - 1) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ a ∈ L1, (L2.filter (H.Adj a)).card := Finset.sum_le_sum hper
  have hL1_L2 : (d - 2) * L1.card ≤ 2 * L2.card := by
    have : (d - 1) * L1.card = (d - 2) * L1.card + L1.card := by
      have h : d - 1 = (d - 2) + 1 := by omega
      rw [h]; ring
    omega
  have hL1_le_L2 : L1.card ≤ L2.card := by
    have : 3 * L1.card ≤ (d - 2) * L1.card := Nat.mul_le_mul_right _ (by omega)
    omega
  -- Choose a parent π b ∈ L1 for each b ∈ L2
  let π : W → W := fun b =>
    if hb : b ∈ L2 then Classical.choose (Finset.mem_filter.mp hb).2 else v₀
  have hπ : ∀ b ∈ L2, π b ∈ L1 ∧ H.Adj (π b) b := fun b hb => by
    dsimp only [π]
    rw [dif_pos hb]
    exact Classical.choose_spec (Finset.mem_filter.mp hb).2
  let L2a : W → Finset W := fun a => L2.filter (fun b => π b = a)
  let L3a : W → Finset W := fun a => L3.filter (fun c => ∃ b ∈ L2a a, H.Adj b c)
  -- Buckets L3a are pairwise disjoint for distinct a₁, a₂ ∈ L1
  have hL3a_disj : (L1 : Set W).PairwiseDisjoint L3a := by
    intro a₁ ha₁ a₂ ha₂ ha12
    refine Finset.disjoint_left.mpr fun c hc₁ hc₂ => ?_
    have hc3 : c ∈ L3 := (Finset.mem_filter.mp hc₁).1
    obtain ⟨b₁, hb₁, hbc₁⟩ := (Finset.mem_filter.mp hc₁).2
    obtain ⟨b₂, hb₂, hbc₂⟩ := (Finset.mem_filter.mp hc₂).2
    have hb₁L2 : b₁ ∈ L2 := (Finset.mem_filter.mp hb₁).1
    have hb₂L2 : b₂ ∈ L2 := (Finset.mem_filter.mp hb₂).1
    have hπ₁ : π b₁ = a₁ := (Finset.mem_filter.mp hb₁).2
    have hπ₂ : π b₂ = a₂ := (Finset.mem_filter.mp hb₂).2
    have hb12 : b₁ ≠ b₂ := fun h => ha12 (by rw [← hπ₁, ← hπ₂, h])
    have ha₁b₁ : H.Adj a₁ b₁ := hπ₁ ▸ (hπ b₁ hb₁L2).2
    have ha₂b₂ : H.Adj a₂ b₂ := hπ₂ ▸ (hπ b₂ hb₂L2).2
    exact hfree (mk_c6 H v₀ a₁ b₁ c b₂ a₂
      (fun h => hv0_nL1 (h ▸ ha₁)) (fun h => hv0_nL2 (h ▸ hb₁L2))
      (fun h => hv0_nL3 (h ▸ hc3)) (fun h => hv0_nL2 (h ▸ hb₂L2))
      (fun h => hv0_nL1 (h ▸ ha₂))
      (h12_disj a₁ ha₁ b₁ hb₁L2) (h13_disj a₁ ha₁ c hc3) (h12_disj a₁ ha₁ b₂ hb₂L2) ha12
      (h23_disj b₁ hb₁L2 c hc3) hb12 (h12_disj a₂ ha₂ b₁ hb₁L2).symm
      (h23_disj b₂ hb₂L2 c hc3).symm (h13_disj a₂ ha₂ c hc3).symm
      (h12_disj a₂ ha₂ b₂ hb₂L2).symm
      (Finset.mem_filter.mp ha₁).2 ha₁b₁ hbc₁ hbc₂.symm ha₂b₂.symm (Finset.mem_filter.mp ha₂).2.symm)
  have hL3a_sum : ∑ a ∈ L1, (L3a a).card ≤ Fintype.card W := by
    rw [← Finset.card_biUnion hL3a_disj]
    exact Finset.card_le_univ _
  have hL2a_sum : ∑ a ∈ L1, (L2a a).card = L2.card := by
    symm
    exact Finset.card_eq_sum_card_fiberwise (fun b hb => (hπ b hb).1)
  -- Apply no_P5_bipartite_edges to each (L2a a, L3a a)
  have hE23_per : ∀ a ∈ L1,
      ∑ b ∈ L2a a, (L3.filter (H.Adj b)).card ≤ 2 * (L3a a).card + (L2a a).card := by
    intro a ha
    have hfilt_eq : ∀ b ∈ L2a a, (L3.filter (H.Adj b)).card = ((L3a a).filter (H.Adj b)).card := by
      intro b hb
      congr 1; ext c
      simp only [L3a, Finset.mem_filter]
      exact ⟨fun ⟨hc, hbc⟩ => ⟨⟨hc, ⟨b, hb, hbc⟩⟩, hbc⟩, fun ⟨⟨hc, _⟩, hbc⟩ => ⟨hc, hbc⟩⟩
    rw [Finset.sum_congr rfl hfilt_eq]
    apply no_P5_bipartite_edges H (L2a a) (L3a a)
    intro b₁ hb₁ b₂ hb₂ b₃ hb₃ c₁ hc₁ c₂ hc₂ hb12 hb23 hb13 hc12 e1 e2 e3 e4
    have hb₁L2 : b₁ ∈ L2 := (Finset.mem_filter.mp hb₁).1
    have hb₂L2 : b₂ ∈ L2 := (Finset.mem_filter.mp hb₂).1
    have hb₃L2 : b₃ ∈ L2 := (Finset.mem_filter.mp hb₃).1
    have hc₁L3 : c₁ ∈ L3 := (Finset.mem_filter.mp hc₁).1
    have hc₂L3 : c₂ ∈ L3 := (Finset.mem_filter.mp hc₂).1
    have hab₁ : H.Adj a b₁ := (Finset.mem_filter.mp hb₁).2 ▸ (hπ b₁ hb₁L2).2
    have hab₃ : H.Adj a b₃ := (Finset.mem_filter.mp hb₃).2 ▸ (hπ b₃ hb₃L2).2
    exact hfree (mk_c6 H a b₁ c₁ b₂ c₂ b₃
      (h12_disj a ha b₁ hb₁L2) (h13_disj a ha c₁ hc₁L3) (h12_disj a ha b₂ hb₂L2)
      (h13_disj a ha c₂ hc₂L3) (h12_disj a ha b₃ hb₃L2)
      (h23_disj b₁ hb₁L2 c₁ hc₁L3) hb12 (h23_disj b₁ hb₁L2 c₂ hc₂L3) hb13
      (h23_disj b₂ hb₂L2 c₁ hc₁L3).symm hc12 (h23_disj b₃ hb₃L2 c₁ hc₁L3).symm
      (h23_disj b₂ hb₂L2 c₂ hc₂L3) hb23 (h23_disj b₃ hb₃L2 c₂ hc₂L3).symm
      hab₁ e1 e2.symm e3 e4.symm hab₃.symm)
  -- Sum E23 over L2 via fiberwise partition into L2a
  have hE23_up : ∑ b ∈ L2, (L3.filter (H.Adj b)).card ≤ 2 * Fintype.card W + L2.card := by
    have hfib : ∑ b ∈ L2, (L3.filter (H.Adj b)).card =
        ∑ a ∈ L1, ∑ b ∈ L2a a, (L3.filter (H.Adj b)).card :=
      (Finset.sum_fiberwise_of_maps_to (g := π) (t := L1) (fun b hb => (hπ b hb).1) _).symm
    rw [hfib]
    calc ∑ a ∈ L1, ∑ b ∈ L2a a, (L3.filter (H.Adj b)).card
        ≤ ∑ a ∈ L1, (2 * (L3a a).card + (L2a a).card) := Finset.sum_le_sum hE23_per
      _ = 2 * (∑ a ∈ L1, (L3a a).card) + ∑ a ∈ L1, (L2a a).card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ 2 * Fintype.card W + L2.card := by rw [hL2a_sum]; omega
  -- Lower bound E12 + E23 ≥ d * L2.card
  have hE12_swap : ∑ b ∈ L2, (L1.filter (H.Adj b)).card = ∑ a ∈ L1, (L2.filter (H.Adj a)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : H.Adj b a
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have hL2_deg : d * L2.card ≤ (∑ a ∈ L1, (L2.filter (H.Adj a)).card) +
      (∑ b ∈ L2, (L3.filter (H.Adj b)).card) := by
    rw [← hE12_swap, ← Finset.sum_add_distrib]
    have hper : ∀ b ∈ L2, d ≤ (L1.filter (H.Adj b)).card + (L3.filter (H.Adj b)).card := by
      intro b hb
      have hbU : b ∈ U := (Finset.mem_erase.mp (Finset.mem_filter.mp hb).1).2
      have hsub : U.filter (H.Adj b) ⊆ L1.filter (H.Adj b) ∪ L3.filter (H.Adj b) := by
        intro x hx
        have hxU : x ∈ U := (Finset.mem_filter.mp hx).1
        have hbx : H.Adj b x := (Finset.mem_filter.mp hx).2
        by_cases hx1 : x ∈ L1
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx1, hbx⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hxU, hx1⟩, ⟨b, hb, hbx⟩⟩, hbx⟩)
      have h1 := hmin b hbU
      have h2 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      omega
    calc d * L2.card = ∑ _b ∈ L2, d := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ b ∈ L2, ((L1.filter (H.Adj b)).card + (L3.filter (H.Adj b)).card) := Finset.sum_le_sum hper
  have hstep1 : (d - 4) * L2.card ≤ 2 * Fintype.card W := by
    have : d * L2.card = (d - 4) * L2.card + 4 * L2.card := by
      have h : d = (d - 4) + 4 := by omega
      nth_rw 1 [h]; ring
    omega
  have hstep2 : (d - 2) * d ≤ 2 * L2.card :=
    (Nat.mul_le_mul_left (d - 2) hL1_card).trans hL1_L2
  calc (d - 4) * (d - 2) * d = (d - 4) * ((d - 2) * d) := by ring
    _ ≤ (d - 4) * (2 * L2.card) := Nat.mul_le_mul_left _ hstep2
    _ = 2 * ((d - 4) * L2.card) := by ring
    _ ≤ 2 * (2 * Fintype.card W) := Nat.mul_le_mul_left 2 hstep1
    _ = 4 * Fintype.card W := by ring

/-- Concrete Bondy–Simonovits upper bound `ex(n, C₆)³ ≤ 20³ * n⁴` for all `n ≥ 1`. -/
theorem c6_upper_bound (n : ℕ) (hn : 1 ≤ n) :
    (extremalNumber n (cycleGraph 6)) ^ 3 ≤ 20 ^ 3 * n ^ 4 := by
  have nb : cycleGraph 6 ≠ ⊥ := by
    intro h
    have hadj : (cycleGraph 6).Adj (0 : Fin 6) 1 := by decide
    rw [h] at hadj
    exact hadj
  obtain ⟨X, _, ext⟩ := exists_isExtremal_free (V := Fin n) nb
  obtain ⟨hfree, hcard⟩ := isExtremal_free_iff.mp ext
  rw [Fintype.card_fin] at hcard
  obtain ⟨S, H, hHX, hbip, hhalf⟩ := exists_bipartite_sub X
  have hhalf' : extremalNumber n (cycleGraph 6) ≤ 2 * H.edgeFinset.card := by
    refine le_trans (le_of_eq ?_) hhalf
    rw [← hcard]
    congr! 2
  have hHfree : (cycleGraph 6).Free H := fun ⟨e⟩ =>
    hfree ⟨⟨⟨e, fun {u v} h => hHX (e.toHom.map_rel' h)⟩, e.injective⟩⟩
  by_cases hsmall : H.edgeFinset.card ≤ 10 * n
  · have he : extremalNumber n (cycleGraph 6) ≤ 20 * n := by omega
    calc (extremalNumber n (cycleGraph 6)) ^ 3 ≤ (20 * n) ^ 3 := Nat.pow_le_pow_left he 3
      _ = 20 ^ 3 * n ^ 3 := by ring
      _ ≤ 20 ^ 3 * n ^ 4 := Nat.mul_le_mul_left _ (by
          have : n ^ 3 * 1 ≤ n ^ 3 * n := Nat.mul_le_mul_left _ hn
          linarith [show n ^ 3 * n = n ^ 4 by ring])
  · push Not at hsmall
    let d := (H.edgeFinset.card - 1) / n
    have hd10 : 10 ≤ d := by
      dsimp [d]
      exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hlt : d * Fintype.card (Fin n) < H.edgeFinset.card := by
      rw [Fintype.card_fin]
      have hdiv : d * n ≤ H.edgeFinset.card - 1 := Nat.div_mul_le_self _ _
      omega
    obtain ⟨U, hne, hmin⟩ := exists_min_deg_sub H d hlt
    have hbfs := c6_free_bipartite_min_deg H S hbip hHfree U hne (d + 1) (by omega) hmin
    rw [Fintype.card_fin] at hbfs
    have hd_half : d + 1 ≤ 2 * (d + 1 - 4) := by omega
    have hd_cube : (d + 1) ^ 3 ≤ 32 * n := by
      have h4 : d + 1 - 4 + 4 = d + 1 := by omega
      have h2 : d + 1 - 2 + 2 = d + 1 := by omega
      have hge7 : 7 ≤ d + 1 - 4 := by omega
      have hsq : (d + 1) ^ 2 ≤ 4 * ((d + 1 - 4) * (d + 1 - 2)) := by nlinarith
      have h1 : (d + 1) ^ 3 ≤ 8 * ((d + 1 - 4) * (d + 1 - 2) * (d + 1)) := by nlinarith
      omega
    have hH_le : H.edgeFinset.card ≤ (d + 1) * n := by
      have h1 : H.edgeFinset.card - 1 < (d + 1) * n := by
        dsimp [d]
        have := Nat.lt_mul_div_succ (H.edgeFinset.card - 1) (by omega : 0 < n)
        linarith
      omega
    have he_le : extremalNumber n (cycleGraph 6) ≤ 2 * (d + 1) * n := by
      have : 2 * ((d + 1) * n) = 2 * (d + 1) * n := by ring
      omega
    have hcube := Nat.pow_le_pow_left he_le 3
    calc (extremalNumber n (cycleGraph 6)) ^ 3 ≤ (2 * (d + 1) * n) ^ 3 := hcube
      _ = 8 * (d + 1) ^ 3 * n ^ 3 := by ring
      _ ≤ 8 * (32 * n) * n ^ 3 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 hd_cube)
      _ = 256 * n ^ 4 := by ring
      _ ≤ 20 ^ 3 * n ^ 4 := Nat.mul_le_mul_right _ (by decide)

end E713BondySimonovits

end

section

open SimpleGraph Finset Filter Asymptotics Real
open scoped Classical

namespace E713FourThirds

lemma rpow_four_thirds_cube (n : ℕ) (hn : 0 < (n : ℝ)) :
    ((n : ℝ) ^ (4 / 3 : ℝ)) ^ 3 = (n : ℝ) ^ 4 := by
  rw [← Real.rpow_natCast ((n : ℝ) ^ (4 / 3 : ℝ)) 3, ← Real.rpow_mul hn.le]
  norm_num

theorem c6_lower {V : Type*} (F : SimpleGraph V) (sub : cycleGraph 6 ⊑ F) :
    (fun n : ℕ => (n : ℝ) ^ (4 / 3 : ℝ)) =O[atTop] (fun n : ℕ => (extremalNumber n F : ℝ)) := by
  apply isBigO_iff.mpr
  refine ⟨64, ?_⟩
  filter_upwards [eventually_ge_atTop (54 : ℕ)] with n hn
  have pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmono : extremalNumber n (cycleGraph 6) ≤ extremalNumber n F := E713Exponents.mono_ex sub n
  have hnat : n ^ 4 ≤ 64 ^ 3 * (extremalNumber n F) ^ 3 :=
    (E713Wenger.c6_lower_uniform n hn).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmono 3))
  have hreal : (n : ℝ) ^ 4 ≤ (64 * (extremalNumber n F : ℝ)) ^ 3 := by
    rw [mul_pow]
    exact_mod_cast hnat
  rw [← rpow_four_thirds_cube n pos] at hreal
  have hle : (n : ℝ) ^ (4 / 3 : ℝ) ≤ 64 * (extremalNumber n F : ℝ) :=
    le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by positivity) hreal
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg pos.le _),
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact hle

theorem c6_sub_upper {V : Type*} (F : SimpleGraph V) (sub : F ⊑ cycleGraph 6) :
    (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (4 / 3 : ℝ)) := by
  apply isBigO_iff.mpr
  refine ⟨20, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmono : extremalNumber n F ≤ extremalNumber n (cycleGraph 6) := E713Exponents.mono_ex sub n
  have hnat : (extremalNumber n F) ^ 3 ≤ 20 ^ 3 * n ^ 4 :=
    (Nat.pow_le_pow_left hmono 3).trans (E713BondySimonovits.c6_upper_bound n hn)
  have hreal : (extremalNumber n F : ℝ) ^ 3 ≤ (20 * (n : ℝ) ^ (4 / 3 : ℝ)) ^ 3 := by
    rw [mul_pow, rpow_four_thirds_cube n pos]
    exact_mod_cast hnat
  have hle : (extremalNumber n F : ℝ) ≤ 20 * (n : ℝ) ^ (4 / 3 : ℝ) :=
    le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by positivity) hreal
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg pos.le _)]
  exact hle

/-- Matching `Θ(n^(4/3))` bound for the six-cycle `C₆`. -/
theorem c6_theta :
    (fun n : ℕ => (extremalNumber n (cycleGraph 6) : ℝ)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (4 / 3 : ℝ)) :=
  ⟨c6_sub_upper (cycleGraph 6) (SimpleGraph.IsContained.refl (cycleGraph 6)),
   c6_lower (cycleGraph 6) (SimpleGraph.IsContained.refl (cycleGraph 6))⟩

end E713FourThirds

end

open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology

namespace OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1_H2_R1_H1_R1

/-- Below exponent `4/3` (in `(1, 4/3)`) the forbidden graph must be both `C₄`-free and `C₆`-free. -/
def H1 : Prop := ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.Connected → G.IsBipartite →
    (∀ v, 2 ≤ G.degree v) → (completeBipartiteGraph (Fin 2) (Fin 2)).Free G →
    (cycleGraph 6).Free G →
    ∀ α : ℝ, α ∈ Set.Ioo 1 (4 / 3 : ℝ) →
      (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      ¬ (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      α ∈ Set.range ((↑) : ℚ → ℝ)

/-- Above exponent `4/3` (in `(4/3, 3/2)`) the forbidden `C₄`-free graph cannot embed into `C₆`. -/
def H2 : Prop := ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.Connected → G.IsBipartite →
    (∀ v, 2 ≤ G.degree v) → (completeBipartiteGraph (Fin 2) (Fin 2)).Free G →
    ¬ (G ⊑ cycleGraph 6) →
    ∀ α : ℝ, α ∈ Set.Ioo (4 / 3 : ℝ) (3 / 2 : ℝ) →
      (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      ¬ (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      α ∈ Set.range ((↑) : ℚ → ℝ)

theorem main : H1 → H2 → OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1_H2_R1.H1 := by
  intro small large q G conn bip minDeg c4free α range big sharp
  rcases lt_trichotomy α (4 / 3 : ℝ) with lt | eq | gt
  · apply small q G conn bip minDeg c4free _ α ⟨range.1, lt⟩ big sharp
    intro sub
    have impossible :=
      ((E713FourThirds.c6_lower G sub).trans big).trans_isLittleO (E713Exponents.smaller lt)
    have nonzero : ∃ᶠ n : ℕ in atTop, (n : ℝ) ^ (4 / 3 : ℝ) ≠ 0 :=
      ((eventually_gt_atTop (0 : ℕ)).mono fun n hn =>
        (Real.rpow_pos_of_pos (by exact_mod_cast hn) _).ne').frequently
    exact isLittleO_irrefl nonzero impossible
  · exact ⟨(4 / 3 : ℚ), by push_cast; linarith⟩
  · apply large q G conn bip minDeg c4free _ α ⟨gt, range.2⟩ big sharp
    intro sub
    exact sharp ((E713FourThirds.c6_sub_upper G sub).trans_isLittleO (E713Exponents.smaller gt))

end OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1_H2_R1_H1_R1
