import OMAStatements.S_mse_4084662

-- Take the countable union of bounded-support subspaces of a product of real lines.
-- Its size is beth omega, and every metric space of that size embeds using distance bumps.

namespace LTS4084662Count

open Cardinal

abbrev A (n : ℕ) : Type := (beth (n : Ordinal)).out
abbrev K : Type := Σ n : ℕ, A n
abbrev I : Type := K × ℕ
noncomputable abbrev kappa : Cardinal.{0} := beth Ordinal.omega0

abbrev Bounded : Type := {f : I → ℝ // ∃ N : ℕ, ∀ i, N < i.1.1 → f i = 0}
abbrev Stage (N : ℕ) : Type := {f : I → ℝ // ∀ i, N < i.1.1 → f i = 0}
abbrev StageDomain (N : ℕ) : Type := {i : I // i.1.1 ≤ N}

theorem beth_nat_lt (n : ℕ) : beth (n : Ordinal) < kappa :=
  beth_strictMono (Ordinal.natCast_lt_omega0 n)

theorem kappa_large : ℵ₀ < kappa := by
  simpa only [Nat.cast_zero, beth_zero] using beth_nat_lt 0

theorem sum_beth : Cardinal.sum (fun n : ℕ => beth (n : Ordinal)) = kappa := by
  have hs : (⨆ n : ℕ, beth (n : Ordinal)) = kappa := by
    refine le_antisymm (ciSup_le' fun n => (beth_nat_lt n).le) ?_
    rw [show kappa = beth Ordinal.omega0 from rfl, beth_limit Ordinal.isSuccLimit_omega0]
    apply ciSup_le'
    intro o
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp o.property
    simpa only [hn] using
      (le_ciSup (f := fun n : ℕ => beth (n : Ordinal)) bddAbove_of_small n)
  calc
    Cardinal.sum (fun n : ℕ => beth (n : Ordinal)) = ⨆ n : ℕ, beth (n : Ordinal) :=
      sum_eq_iSup_of_mk_le_iSup (by rw [mk_nat]) (by rw [mk_nat, hs]; exact kappa_large.le)
    _ = kappa := hs

theorem mk_K : Cardinal.mk K = kappa := by
  rw [mk_sigma]
  simpa only [A, mk_out] using sum_beth

theorem kappa_power_ne : kappa ^ ℵ₀ ≠ kappa := by
  have h : kappa < kappa ^ ℵ₀ := calc
    kappa = Cardinal.sum (fun n : ℕ => beth (n : Ordinal)) := sum_beth.symm
    _ < Cardinal.prod (fun n : ℕ => beth (↑(n + 1) : Ordinal)) :=
      sum_lt_prod _ _ (fun n => beth_strictMono (by exact_mod_cast Nat.lt_succ_self n))
    _ ≤ Cardinal.prod (fun _ : ℕ => kappa) := prod_le_prod _ _ (fun n => (beth_nat_lt (n + 1)).le)
    _ = kappa ^ ℵ₀ := by rw [prod_const', mk_nat]
  exact h.ne'

theorem mk_stage_domain_le (N : ℕ) : Cardinal.mk (StageDomain N) ≤ beth (N : Ordinal) := by
  classical
  let embed (n : ℕ) (h : n ≤ N) : A n ↪ A N :=
    Classical.choice ((le_def _ _).mp (by
      simpa only [A, mk_out] using
        (beth_mono (by exact_mod_cast h) : beth (n : Ordinal) ≤ beth (N : Ordinal))))
  let pack : StageDomain N → ℕ × A N × ℕ :=
    fun i => (i.1.1.1, embed i.1.1.1 i.2 i.1.1.2, i.1.2)
  have hpack : Function.Injective pack := by
    rintro ⟨⟨⟨m, x⟩, i⟩, hm⟩ ⟨⟨⟨n, y⟩, j⟩, hn⟩ h
    have hmn : m = n := congrArg Prod.fst h
    subst n
    have hxy : embed m hm x = embed m hm y := congrArg (fun z : ℕ × A N × ℕ => z.2.1) h
    have hij : i = j := congrArg (fun z : ℕ × A N × ℕ => z.2.2) h
    have hval : x = y := (embed m hm).injective hxy
    subst y
    subst j
    rfl
  calc
    Cardinal.mk (StageDomain N) ≤ Cardinal.mk (ℕ × A N × ℕ) := mk_le_of_injective hpack
    _ = beth (N : Ordinal) := by
      simp only [mk_prod, lift_id, mk_nat, A, mk_out]
      rw [mul_eq_left (aleph0_le_beth _) (aleph0_le_beth _) aleph0_ne_zero,
        mul_eq_right (aleph0_le_beth _) (aleph0_le_beth _) aleph0_ne_zero]

theorem mk_stage_le (N : ℕ) : Cardinal.mk (Stage N) ≤ beth (↑(N + 1) : Ordinal) := by
  let restrict : Stage N → StageDomain N → ℝ := fun f i => f.1 i.1
  have hres : Function.Injective restrict := by
    intro f g hfg
    apply Subtype.ext
    funext i
    obtain hi | hi := lt_or_ge N i.1.1
    · exact (f.2 i hi).trans (g.2 i hi).symm
    · exact congrFun hfg ⟨i, hi⟩
  calc
    Cardinal.mk (Stage N) ≤ Cardinal.mk (StageDomain N → ℝ) := mk_le_of_injective hres
    _ = 𝔠 ^ Cardinal.mk (StageDomain N) := by simp only [mk_arrow, lift_id, mk_real]
    _ ≤ 𝔠 ^ beth (N : Ordinal) := power_le_power_left continuum_ne_zero (mk_stage_domain_le N)
    _ = beth (↑(N + 1) : Ordinal) := by
      rw [Nat.cast_add, Nat.cast_one, beth_add_one, ← two_power_aleph0, ← power_mul,
        mul_eq_right (aleph0_le_beth _) (aleph0_le_beth _) aleph0_ne_zero]

theorem mk_bounded : Cardinal.mk Bounded = kappa := by
  classical
  refine le_antisymm ?_ ?_
  · let combine : (Σ N, Stage N) → Bounded := fun p => ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
    have hcombine : Function.Surjective combine := by
      rintro ⟨f, N, hN⟩
      exact ⟨⟨N, ⟨f, hN⟩⟩, rfl⟩
    calc
      Cardinal.mk Bounded ≤ Cardinal.mk (Σ N, Stage N) := mk_le_of_surjective hcombine
      _ = Cardinal.sum (fun N => Cardinal.mk (Stage N)) := mk_sigma _
      _ ≤ Cardinal.sum (fun _ : ℕ => kappa) :=
        sum_le_sum _ _ fun N => (mk_stage_le N).trans (beth_nat_lt (N + 1)).le
      _ = kappa := by rw [sum_const', mk_nat, mul_eq_right kappa_large.le kappa_large.le aleph0_ne_zero]
  · rw [← mk_K]
    let point : K → Bounded := fun x =>
      ⟨fun i => if i = (x, 0) then 1 else 0, x.1, by
        intro i hi
        have hne : i ≠ (x, 0) := by
          rintro rfl
          exact lt_irrefl _ hi
        simp only [hne, ite_false]⟩
    apply mk_le_of_injective (f := point)
    intro x y h
    by_contra hne
    have hpair : (x, (0 : ℕ)) ≠ (y, 0) := fun heq => hne (congrArg Prod.fst heq)
    have heval := congrFun (congrArg Subtype.val h) (x, 0)
    simp [point, hpair] at heval

end LTS4084662Count

open Set Filter Topology

theorem universalEmbedding {A : ℕ → Type} {Y : Type} [MetricSpace Y]
    (e : Y ≃ (Σ n : ℕ, A n)) :
    ∃ f : Y → {g : ((Σ n : ℕ, A n) × ℕ) → ℝ //
      ∃ N : ℕ, ∀ i, N < i.1.1 → g i = 0}, Topology.IsEmbedding f := by
  classical
  let C := (Σ n : ℕ, A n) × ℕ
  let U := {g : C → ℝ // ∃ N : ℕ, ∀ i : C, N < i.1.1 → g i = 0}
  let rank (y : Y) := (e y).1
  let center (i : C) := e.symm i.1
  let radius (i : C) : ℝ := 1 / ((i.2 : ℝ) + 1)
  let allowed (i : C) := ∀ y : Y, rank y < i.1.1 → radius i ≤ dist y (center i)
  let coordinate (y : Y) (i : C) : ℝ :=
    if allowed i then max 0 (radius i - dist y (center i)) else 0
  have hbounded (y : Y) : ∃ N : ℕ, ∀ i : C, N < i.1.1 → coordinate y i = 0 := by
    refine ⟨rank y, fun i hi ↦ ?_⟩
    by_cases h : allowed i
    · simp [coordinate, h, max_eq_left (sub_nonpos.mpr (h y hi))]
    · simp [coordinate, h]
  let f (y : Y) : U := ⟨coordinate y, hbounded y⟩
  have hf : Continuous f := by
    have hc : Continuous coordinate := continuous_pi fun i ↦ by
      by_cases h : allowed i
      · simpa [coordinate, h] using
          (continuous_const.max (continuous_const.sub
            (continuous_id.dist continuous_const)) :
            Continuous (fun y : Y ↦ max (0 : ℝ) (radius i - dist y (center i))))
      · simpa [coordinate, h] using (continuous_const : Continuous (fun _ : Y ↦ (0 : ℝ)))
    exact hc.subtype_mk hbounded
  have hlocal (x : Y) (δ : ℝ) (hδ : 0 < δ) :
      ∃ i : C, 0 < (f x).1 i ∧ ∀ y : Y, 0 < (f y).1 i → dist y x < δ := by
    let stage (n : ℕ) : Set Y := {y | rank y ≤ n}
    have hex : ∃ n : ℕ, x ∈ closure (stage n) :=
      ⟨rank x, subset_closure (show rank x ≤ rank x from le_rfl)⟩
    let n := Nat.find hex
    have hxn : x ∈ closure (stage n) := Nat.find_spec hex
    have hxprev : x ∈ (closure {y | rank y < n})ᶜ := by
      by_cases hn : n = 0
      · simp [hn]
      · intro hx
        have hsubset : {y | rank y < n} ⊆ stage (n - 1) := by
          intro y hy
          change rank y < n at hy
          change rank y ≤ n - 1
          omega
        exact Nat.find_min hex (show n - 1 < n by omega) (closure_mono hsubset hx)
    obtain ⟨ρ, hρ, hρsub⟩ :=
      Metric.isOpen_iff.mp isClosed_closure.isOpen_compl x hxprev
    have hmin : 0 < min (δ / 2) (ρ / 2) := lt_min (by positivity) (by positivity)
    obtain ⟨q, hq⟩ := exists_nat_one_div_lt hmin
    let r : ℝ := 1 / ((q : ℝ) + 1)
    have hr : 0 < r := by positivity
    have hrδ : r < δ / 2 := lt_of_lt_of_le hq (min_le_left _ _)
    have hrρ : r < ρ / 2 := lt_of_lt_of_le hq (min_le_right _ _)
    obtain ⟨z, hzn, hxz⟩ := Metric.mem_closure_iff.mp hxn r hr
    let i : C := (e z, q)
    have hcenter : center i = z := e.symm_apply_apply z
    have hradius : radius i = r := rfl
    have hallow : allowed i := by
      intro y hy
      rw [hcenter, hradius]
      by_contra! hyz
      change rank y < rank z at hy
      change rank z ≤ n at hzn
      have hyPrev : y ∈ closure {y | rank y < n} :=
        subset_closure (lt_of_lt_of_le hy hzn)
      have hyBall : y ∈ Metric.ball x ρ := by
        rw [Metric.mem_ball]
        have hyx := dist_triangle y z x
        rw [dist_comm z x] at hyx
        linarith
      exact (hρsub hyBall) hyPrev
    refine ⟨i, ?_, ?_⟩
    · change 0 < coordinate x i
      simpa [coordinate, hallow, hradius, hcenter] using (sub_pos.mpr hxz)
    · intro y hy
      change 0 < coordinate y i at hy
      have hyz : dist y z < r := by
        simpa [coordinate, hallow, hradius, hcenter, sub_pos] using hy
      have hyx := dist_triangle y z x
      rw [dist_comm z x] at hyx
      linarith
  refine ⟨f, ⟨?_, ?_⟩⟩
  · apply Topology.isInducing_iff_nhds.mpr
    intro x
    refine le_antisymm (Filter.map_le_iff_le_comap.mp hf.continuousAt) ?_
    intro s hs
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨i, hix, hi⟩ := hlocal x δ hδ
    have hopen : IsOpen {g : U | 0 < g.1 i} :=
      isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val)
    refine Filter.mem_of_superset (Filter.preimage_mem_comap (hopen.mem_nhds hix)) ?_
    intro y hy
    exact hsub (hi y hy)
  · intro x y heq
    by_contra hne
    obtain ⟨i, hix, hi⟩ := hlocal x (dist y x) (dist_pos.mpr (Ne.symm hne))
    rw [heq] at hix
    exact (lt_irrefl _ (hi y hix))

open LTS4084662Count in
theorem OMA.solution : type_of% @OMA.S_mse_4084662.main := by
  classical
  refine ⟨kappa, kappa_large, kappa_power_ne, Bounded, inferInstance, mk_bounded, ?_⟩
  intro Y _ hY
  let e : Y ≃ K := Classical.choice (Cardinal.eq.mp (hY.trans mk_K.symm))
  exact universalEmbedding e
