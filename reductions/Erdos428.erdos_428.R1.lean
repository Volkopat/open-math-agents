import FormalConjectures.ErdosProblems.«428»

/-! A finite packing and tightness reduction for Erdős problem 428. -/

-- Credit: @Pixelstorm44
namespace OMA.R_Erdos428_erdos_428_R1

open Set Filter Erdos428

/-- Arbitrarily large finite sets of centers pass a uniform prefix counting test.
At x the test counts all positive offsets up to x compatible with every center. -/
def H1 : Prop :=
  ∃ D N : ℕ, 0 < D ∧ ∀ k : ℕ, ∃ t : Finset ℕ, k ≤ t.card ∧
    ∀ x ≥ N, (∃ n ∈ t, x < n) → Nat.primeCounting x ≤ D *
      ((Finset.Icc 1 x).filter (fun a => ∀ n ∈ t, a < n → (n - a).Prime)).card

/-- A tightness estimate for finite configurations. If a fixed set of centers
has arbitrarily large feasible extensions, some bounded window past L can
still be hit by arbitrarily large feasible extensions. -/
def H2 : Prop :=
  ∀ D N : ℕ, 0 < D →
    let good := fun t : Finset ℕ => ∀ x ≥ N, (∃ n ∈ t, x < n) →
      Nat.primeCounting x ≤ D *
        ((Finset.Icc 1 x).filter (fun a => ∀ n ∈ t, a < n → (n - a).Prime)).card
    ∀ s : Finset ℕ, (∀ k : ℕ, ∃ t : Finset ℕ, s ⊆ t ∧ k ≤ t.card ∧ good t) →
      ∀ L : ℕ, ∃ B : ℕ, ∀ k : ℕ, ∃ t : Finset ℕ,
        s ⊆ t ∧ k ≤ t.card ∧ good t ∧ ∃ m ∈ t, L ≤ m ∧ m ≤ B

/-- The finite packing condition is necessary for a positive answer. -/
lemma packing_necessary (A : Set ℕ)
    (hw : ∃ᶠ n in atTop, ∀ a ∈ A, 0 < a → a < n → (n-a).Prime)
    (hd : 0 < liminf (primeDensityRatio A) atTop) : H1 := by
  obtain ⟨d, hd'⟩ := exists_nat_one_div_lt hd
  have hnonneg : atTop.IsBoundedUnder (· ≥ ·) (primeDensityRatio A) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ x : ℕ in atTop, 0 ≤ primeDensityRatio A x
    apply Eventually.of_forall
    intro x
    unfold primeDensityRatio
    positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_lt_liminf hd' hnonneg)
  refine ⟨d+1, max N 2, by omega, fun k => ?_⟩
  obtain ⟨t, ht, hsize⟩ := (Nat.frequently_atTop_iff_infinite.mp hw).exists_subset_card_eq k
  refine ⟨t, hsize.ge, fun x hx _ => ?_⟩
  let offsets := (Finset.Icc 1 x).filter (fun a => ∀ n ∈ t, a < n → (n-a).Prime)
  have hsub : A ∩ Icc 1 x ⊆ (offsets : Set ℕ) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ha.2,
      fun n hn => ht hn a ha.1 ha.2.1⟩
  have hc := Set.ncard_le_ncard hsub offsets.finite_toSet
  rw [Set.ncard_coe_finset] at hc
  have hpi : 0 < Nat.primeCounting x := by
    rw [← Nat.primesLE_card_eq_primeCounting, Finset.card_pos]
    exact ⟨2, Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩⟩
  have hratio := (hN x (by omega)).le
  unfold primeDensityRatio at hratio
  have hreal := (div_le_div_iff₀ (by positivity) (by exact_mod_cast hpi)).mp hratio
  rw [one_mul, mul_comm] at hreal
  exact (show Nat.primeCounting x ≤ (d+1) * (A ∩ Icc 1 x).ncard by exact_mod_cast hreal).trans
    (Nat.mul_le_mul_left (d+1) hc)

/-- At the position just before a witness, reflection injects the offsets
into the primes in the same interval. This supplies real-liminf coboundedness. -/
lemma ratio_before_witness (A : Set ℕ) (n : ℕ)
    (hn : ∀ a ∈ A, 0 < a → a < n → (n - a).Prime) :
    primeDensityRatio A (n-1) ≤ 1 := by
  have hc : (A ∩ Icc 1 (n-1)).ncard ≤ ((Nat.primesLE (n-1) : Finset ℕ) : Set ℕ).ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun a => n - a)
    · intro a ha
      obtain ⟨hA, hlo, hhi⟩ := ha
      exact Nat.mem_primesLE.mpr ⟨by omega, hn a hA (by omega) (by omega)⟩
    · intro a ha b hb he
      have ha' := ha.2.2
      have hb' := hb.2.2
      dsimp at he
      omega
  rw [Set.ncard_coe_finset, Nat.primesLE_card_eq_primeCounting] at hc
  exact div_le_one_of_le₀ (by exact_mod_cast hc) (by positivity)

/-- The packing test with D = 1 fails as soon as there are two
centers m > n ≥ 4 with n-1 in the tested range. Equality at n-1
would force both offsets n-2 and n-3 to survive at m. -/
lemma two_centers_strict_loss (t : Finset ℕ) {n m : ℕ}
    (hn : n ∈ t) (hm : m ∈ t) (h4 : 4 ≤ n) (hnm : n < m) :
    ((Finset.Icc 1 (n-1)).filter (fun a => ∀ v ∈ t, a < v → (v-a).Prime)).card <
      Nat.primeCounting (n-1) := by
  let s := (Finset.Icc 1 (n-1)).filter (fun a => ∀ v ∈ t, a < v → (v-a).Prime)
  let reflect := fun a => n - a
  have bounds {a : ℕ} (ha : a ∈ s) := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
  have him : s.image reflect ⊆ Nat.primesLE (n-1) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hl, hu⟩ := bounds ha
    exact Nat.mem_primesLE.mpr ⟨by dsimp [reflect]; omega,
      (Finset.mem_filter.mp ha).2 n hn (by omega)⟩
  have hc : (s.image reflect).card = s.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb he
    have ha' := (bounds ha).2
    have hb' := (bounds hb).2
    dsimp [reflect] at he
    omega
  change s.card < _
  rw [← hc, ← Nat.primesLE_card_eq_primeCounting]
  by_contra! hfull
  have heq := Finset.eq_of_subset_of_card_le him hfull
  have lift (p : ℕ) (hp : p.Prime) (hpn : p < n) : (m - n + p).Prime := by
    have hp' : p ∈ s.image reflect := heq.symm ▸ Nat.mem_primesLE.mpr ⟨by omega, hp⟩
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hp'
    have hu := (bounds ha).2
    dsimp [reflect] at he
    have hma := (Finset.mem_filter.mp ha).2 m hm (by omega)
    rwa [show m-a = m-n+p by omega] at hma
  have h2 := (lift 2 Nat.prime_two (by omega)).eq_two_or_odd
  have h3 := (lift 3 Nat.prime_three (by omega)).eq_two_or_odd
  omega

lemma extend_center (good : Finset ℕ → Prop) (s : Finset ℕ) (L B : ℕ)
    (h : ∀ k : ℕ, ∃ t : Finset ℕ, s ⊆ t ∧ k ≤ t.card ∧ good t ∧
      ∃ m ∈ t, L ≤ m ∧ m ≤ B) :
    ∃ m ≥ L, ∀ k : ℕ, ∃ t : Finset ℕ, insert m s ⊆ t ∧ k ≤ t.card ∧ good t := by
  have hf : ∃ᶠ k : ℕ in atTop, ∃ m ∈ Finset.Icc L B,
      ∃ t : Finset ℕ, insert m s ⊆ t ∧ k ≤ t.card ∧ good t := by
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro k
    obtain ⟨t, hst, hk, ht, m, hm, hl, hb⟩ := h k
    exact ⟨m, Finset.mem_Icc.mpr ⟨hl, hb⟩, t, Finset.insert_subset hm hst, hk, ht⟩
  obtain ⟨m, hm, hfreq⟩ := (Finset.Icc L B).frequently_exists.mp hf
  refine ⟨m, (Finset.mem_Icc.mp hm).1, fun k => ?_⟩
  obtain ⟨j, hj, t, hs, hcard, ht⟩ := frequently_atTop.mp hfreq k
  exact ⟨t, hs, hj.trans hcard, ht⟩

theorem main : H1 → H2 → type_of% @Erdos428.erdos_428 := by
  classical
  rintro ⟨D, N, hD, hroot⟩ htight
  let good := fun t : Finset ℕ => ∀ x ≥ N, (∃ n ∈ t, x < n) →
    Nat.primeCounting x ≤ D *
      ((Finset.Icc 1 x).filter (fun a => ∀ n ∈ t, a < n → (n - a).Prime)).card
  let P := fun s : Finset ℕ => ∀ k : ℕ, ∃ t : Finset ℕ, s ⊆ t ∧ k ≤ t.card ∧ good t
  have hempty : P ∅ := by
    intro k
    obtain ⟨t, hk, ht⟩ := hroot k
    exact ⟨t, Finset.empty_subset _, hk, ht⟩
  have step (s : {s // P s}) (L : ℕ) : ∃ m ≥ L, P (insert m s.val) := by
    obtain ⟨B, hB⟩ := htight D N hD s.val s.property L
    exact extend_center good s.val L B hB
  choose nextCenter hlarge hnext using step
  let stages : ℕ → {s // P s} := Nat.rec ⟨∅, hempty⟩
    (fun i s => ⟨insert (nextCenter s i) s.val, hnext s i⟩)
  let S := fun i => (stages i).val
  have grow : Monotone S := monotone_nat_of_le_succ fun i =>
    Finset.subset_insert (nextCenter (stages i) i) _
  have marks (i : ℕ) : ∃ m ∈ S (i+1), i ≤ m :=
    ⟨nextCenter (stages i) i, Finset.mem_insert_self .., hlarge ..⟩
  let A : Set ℕ := {a | ∀ i, ∀ n ∈ S i, a < n → (n-a).Prime}
  have hw : ∃ᶠ n in atTop, ∀ a ∈ A, 0 < a → a < n → (n-a).Prime := by
    apply frequently_atTop.mpr
    intro i
    obtain ⟨m, hm, hi⟩ := marks i
    exact ⟨m, hi, fun a ha _ han => ha (i+1) m hm han⟩
  refine ⟨A, hw, lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (D : ℝ)) ?_⟩
  apply le_liminf_of_le
  · apply IsCoboundedUnder.of_frequently_le (a := (1 : ℝ))
    apply frequently_atTop.mpr
    intro i
    obtain ⟨n, hn, hgood⟩ := frequently_atTop.mp hw (i+1)
    exact ⟨n-1, by omega, ratio_before_witness A n hgood⟩
  · filter_upwards [eventually_ge_atTop (max N 2)] with x hx
    -- Each incompatible offset in this finite interval has a finite obstruction.
    have settled : ∀ᶠ j : ℕ in atTop, ∀ a ∈ Finset.Icc 1 x,
        (∀ m ∈ S j, a < m → (m-a).Prime) → a ∈ A := by
      rw [eventually_all_finset]
      intro a _
      by_cases ha : a ∈ A
      · exact Eventually.of_forall fun _ _ => ha
      · change ¬ ∀ i, ∀ m ∈ S i, a < m → (m-a).Prime at ha
        push Not at ha
        obtain ⟨i, m, hm, ham, hbad⟩ := ha
        filter_upwards [eventually_ge_atTop i] with j hj h
        exact (hbad (h m (grow hj hm) ham)).elim
    obtain ⟨j, hj, hsettled⟩ := ((eventually_ge_atTop (x+2)).and settled).exists
    obtain ⟨m, hm, hxm⟩ := marks (x+1)
    obtain ⟨t, hst, _, ht⟩ := (stages j).property 0
    have hcount := ht x (by omega) ⟨m, hst (grow hj hm), by omega⟩
    let offsets := (Finset.Icc 1 x).filter (fun a => ∀ n ∈ t, a < n → (n-a).Prime)
    have hsub : (offsets : Set ℕ) ⊆ A ∩ Icc 1 x := by
      intro a ha
      obtain ⟨hx', hall⟩ := Finset.mem_filter.mp ha
      exact ⟨hsettled a hx' (fun n hn => hall n (hst hn)), Finset.mem_Icc.mp hx'⟩
    have hcard := Set.ncard_le_ncard hsub ((Set.finite_Icc 1 x).subset Set.inter_subset_right)
    rw [Set.ncard_coe_finset] at hcard
    have hnat : Nat.primeCounting x ≤ D * (A ∩ Icc 1 x).ncard :=
      hcount.trans (Nat.mul_le_mul_left D hcard)
    have hpi : 0 < Nat.primeCounting x := by
      rw [← Nat.primesLE_card_eq_primeCounting, Finset.card_pos]
      exact ⟨2, Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩⟩
    unfold primeDensityRatio
    apply (div_le_div_iff₀ (by exact_mod_cast hD) (by exact_mod_cast hpi)).2
    rw [one_mul, mul_comm]
    exact_mod_cast hnat

end OMA.R_Erdos428_erdos_428_R1
