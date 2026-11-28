import FormalConjectures.ErdosProblems.«78»

/-!
A reduction via the non-oblivious bit-fixing sources of Chattopadhyay and
Zuckerman, Annals of Mathematics 189 (2019), Sections 3, 6 and 7.
A distribution on bit strings has t-wise independent fair bits on its good
coordinates when every cylinder on at most t of them has mass 2^(-|I|).
The other coordinates can depend arbitrarily on the good ones.

Credit: @yuka30240. The ordered split, ceiling bound and final graph argument
are adapted from reduction R1 by @mrmario2202 (PR #4554).
-/

open Filter Real ComplexityTheory Erdos78

namespace OMA.R_Erdos78_erdos_78_variants_cohen_R2

/-- Flat-source case of the sampler in Section 3. For one right vertex of a
large rectangle, the output on a uniform left vertex is within L1 distance
1/4 of a bit-fixing source. Section 7 permits any fixed constant error here. -/
def H1 : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ D > (0 : ℝ),
    ∃ sample : ℕ × ℕ × ℕ → List Bool, IsPolyTime sample ∧
    ∀ M : ℕ, ∀ᶠ n : ℕ in atTop, ∀ A B : Finset (Fin n),
      A.card = ⌈(2 : ℝ) ^ (log (log n)) ^ D⌉₊ →
      B.card = ⌈(2 : ℝ) ^ (log (log n)) ^ D⌉₊ →
      ∃ v ∈ B, ∃ m ≥ M, ∃ G : Finset (Fin m), ∃ w : (Fin m → Bool) → ℝ,
        (∀ z, 0 ≤ w z) ∧ (∑ z, w z) = 1 ∧
        ((m - G.card : ℕ) : ℝ) ≤ (m : ℝ) ^ (1 - δ) ∧
        (∀ I ⊆ G, I.card ≤ (m.log2 + 1) ^ 19 → ∀ a : Fin m → Bool,
          (∑ z : Fin m → Bool, if ∀ i ∈ I, z i = a i then w z else 0) =
            (1 / 2 : ℝ) ^ I.card) ∧
        (∀ u ∈ A, (sample (n, u.val, v.val)).length = m) ∧
        (∑ z : Fin m → Bool, |w z -
          ((A.filter (fun u => sample (n, u.val, v.val) = List.ofFn z)).card : ℝ) /
            A.card|) < 1 / 4

/-- Resilient output function (Sections 4–6). For a polynomially bounded
coalition of bad coordinates and sufficiently high polylogarithmic independence
on the remaining ones, each output fibre has probability at least a quarter.
The exponent 19 absorbs the constant in the log-power 18 of Section 6. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ f : List Bool → Bool, IsPolyTime f ∧
    ∀ᶠ m : ℕ in atTop, ∀ (G : Finset (Fin m)) (w : (Fin m → Bool) → ℝ),
      (∀ z, 0 ≤ w z) → (∑ z, w z) = 1 →
      ((m - G.card : ℕ) : ℝ) ≤ (m : ℝ) ^ (1 - δ) →
      (∀ I ⊆ G, I.card ≤ (m.log2 + 1) ^ 19 → ∀ a : Fin m → Bool,
        (∑ z : Fin m → Bool, if ∀ i ∈ I, z i = a i then w z else 0) =
          (1 / 2 : ℝ) ^ I.card) →
      ∀ b : Bool, (1 / 4 : ℝ) ≤
        ∑ z : Fin m → Bool, if f (List.ofFn z) = b then w z else 0

/-- TM2 composition followed by the unary-size and sorted-label adapter of R1.
The interface is independent of the sampler's probabilistic guarantees. -/
def H3 : Prop :=
  ∀ (sample : ℕ × ℕ × ℕ → List Bool) (f : List Bool → Bool),
    IsPolyTime sample → IsPolyTime f →
    IsPolyTime (fun p : List Bool × ℕ × ℕ =>
      f (sample (p.1.length, min p.2.1 p.2.2, max p.2.1 p.2.2)))

/-- A fibre of a model distribution has a row witness whenever its mass exceeds
the L1 error of the empirical histogram. Repeated row entries are counted. -/
lemma hits_output {m : ℕ} {α : Type*} [DecidableEq α] (A : Finset α)
    (row : α → List Bool) (f : List Bool → Bool) (b : Bool)
    (w : (Fin m → Bool) → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hclose : (∑ z : Fin m → Bool,
      |w z - ((A.filter (fun u => row u = List.ofFn z)).card : ℝ) / A.card|) <
      ∑ z : Fin m → Bool, if f (List.ofFn z) = b then w z else 0) :
    ∃ u ∈ A, f (row u) = b := by
  classical
  by_contra! h
  apply (not_le.mpr hclose)
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : f (List.ofFn z) = b
  · have hempty : A.filter (fun u => row u = List.ofFn z) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro u hu heq
      exact h u hu ((congrArg f heq).trans hz)
    simp [hz, hempty, abs_of_nonneg (hw z)]
  · simp [hz]

lemma ordered_rectangles {n m k : ℕ} (s : Finset (Fin n)) (hs : s.card = m)
    (hm : 2 * k ≤ m) :
    ∃ A B : Finset (Fin n), A ⊆ s ∧ B ⊆ s ∧ A.card = k ∧ B.card = k ∧
      ∀ u ∈ A, ∀ v ∈ B, u < v := by
  let e := s.orderEmbOfFin hs
  let lo (i : Fin k) : Fin m := ⟨i.val, by have := i.isLt; omega⟩
  let hi (i : Fin k) : Fin m := ⟨k + i.val, by have := i.isLt; omega⟩
  have hlo : Function.Injective lo := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin m => x.val) h)
  have hhi : Function.Injective hi := by
    intro i j h
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg (fun x : Fin m => x.val) h)
  let a : Fin k ↪ Fin n := ⟨e ∘ lo, e.injective.comp hlo⟩
  let b : Fin k ↪ Fin n := ⟨e ∘ hi, e.injective.comp hhi⟩
  refine ⟨Finset.univ.map a, Finset.univ.map b, ?_, ?_, by simp, by simp, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact s.orderEmbOfFin_mem hs (lo i)
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact s.orderEmbOfFin_mem hs (hi i)
  · intro u hu v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hv
    change e (lo i) < e (hi j)
    apply e.strictMono
    change i.val < k + j.val
    have := i.isLt
    omega

lemma doubled_ceiling_eventually (D : ℝ) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop,
      2 * ⌈(2 : ℝ) ^ (log (log n)) ^ D⌉₊ ≤
        ⌈(2 : ℝ) ^ (log (log n)) ^ (D + 1)⌉₊ := by
  have ht : Tendsto (fun n : ℕ => log (log n)) atTop atTop :=
    (tendsto_log_atTop.comp tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (3 : ℝ))] with n hn
  let t := log (log (n : ℝ))
  change 3 ≤ t at hn
  have ht1 : 1 ≤ t := by linarith
  have hq : 1 ≤ t ^ D := Real.one_le_rpow ht1 hD.le
  have hx : 1 ≤ (2 : ℝ) ^ (t ^ D) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have hexp : t ^ D + 2 ≤ t ^ (D + 1) := by
    rw [Real.rpow_add (by positivity) D 1, Real.rpow_one]
    calc
      t ^ D + 2 ≤ t ^ D * 3 := by linarith
      _ ≤ t ^ D * t := mul_le_mul_of_nonneg_left hn (by positivity)
  have hpow : (2 : ℝ) ^ (t ^ D) * 4 ≤ (2 : ℝ) ^ (t ^ (D + 1)) := by
    calc
      (2 : ℝ) ^ (t ^ D) * 4 = (2 : ℝ) ^ (t ^ D + 2) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num [Real.rpow_two]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (2 : ℝ) ^ (t ^ D) by positivity)
  change 2 * ⌈(2 : ℝ) ^ (t ^ D)⌉₊ ≤ ⌈(2 : ℝ) ^ (t ^ (D + 1))⌉₊
  exact_mod_cast
    (show 2 * (⌈(2 : ℝ) ^ (t ^ D)⌉₊ : ℝ) ≤ (⌈(2 : ℝ) ^ (t ^ (D + 1))⌉₊ : ℝ) by
      calc
        _ ≤ (2 : ℝ) ^ (t ^ D) * 4 := by linarith
        _ ≤ _ := hpow.trans (Nat.le_ceil _))

theorem main : H1 → H2 → H3 → type_of% @Erdos78.erdos_78.variants.cohen := by
  intro hSampler hResilient hMachine
  obtain ⟨δ, hδ, hδ1, D, hD, sample, hsample, hRows⟩ := hSampler
  obtain ⟨f, hf, hRes⟩ := hResilient δ hδ hδ1
  obtain ⟨M, hM⟩ := eventually_atTop.mp hRes
  let adj := fun p : List Bool × ℕ × ℕ =>
    f (sample (p.1.length, min p.2.1 p.2.2, max p.2.1 p.2.2))
  refine ⟨D + 1, by linarith, adj, hMachine sample f hsample hf, ?_⟩
  filter_upwards [hRows M, doubled_ceiling_eventually D hD] with n hRowsn hsize
  let k := ⌈(2 : ℝ) ^ (log (log n)) ^ D⌉₊
  let m := ⌈(2 : ℝ) ^ (log (log n)) ^ (D + 1)⌉₊
  change 2 * k ≤ m at hsize
  have rectangle (A B : Finset (Fin n)) (hA : A.card = k) (hB : B.card = k)
      (b : Bool) : ∃ u ∈ A, ∃ v ∈ B, f (sample (n, u.val, v.val)) = b := by
    obtain ⟨v, hv, len, hlen, G, w, hw, hmass, hbad, hcyl, _, hclose⟩ :=
      hRowsn A B hA hB
    have hfibre := hM len hlen G w hw hmass hbad hcyl b
    obtain ⟨u, hu, hout⟩ := hits_output A (fun u => sample (n, u.val, v.val))
      f b w hw (lt_of_lt_of_le hclose hfibre)
    exact ⟨u, hu, v, hv, hout⟩
  have hadj (u v : Fin n) (huv : u < v) :
      (explicitGraph adj n).Adj u v ↔ f (sample (n, u.val, v.val)) = true := by
    have hval : u.val ≤ v.val := huv.le
    simp [explicitGraph, adj, min_eq_left hval, max_eq_right hval,
      min_eq_right hval, max_eq_left hval, huv.ne]
  change (explicitGraph adj n).CliqueFree m ∧ (explicitGraph adj n)ᶜ.CliqueFree m
  constructor
  · intro s hs
    obtain ⟨A, B, hA, hB, hAk, hBk, hlt⟩ := ordered_rectangles s hs.card_eq hsize
    obtain ⟨u, hu, v, hv, hfalse⟩ := rectangle A B hAk hBk false
    have huv := hlt u hu v hv
    have htrue := (hadj u v huv).mp (hs.isClique (hA hu) (hB hv) huv.ne)
    simp [hfalse] at htrue
  · intro s hs
    obtain ⟨A, B, hA, hB, hAk, hBk, hlt⟩ := ordered_rectangles s hs.card_eq hsize
    obtain ⟨u, hu, v, hv, htrue⟩ := rectangle A B hAk hBk true
    have huv := hlt u hu v hv
    have hnon := (SimpleGraph.compl_adj _ _ _).mp (hs.isClique (hA hu) (hB hv) huv.ne)
    exact hnon.2 ((hadj u v huv).mpr htrue)

end OMA.R_Erdos78_erdos_78_variants_cohen_R2
