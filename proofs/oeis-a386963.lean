import OMAStatements.S_oeis_a386963
import Mathlib.NumberTheory.Chebyshev

-- Credit: @oh-meh
open OMA.S_oeis_a386963 Filter Topology Finset

private abbrev P (m : ℕ) := Odd m ∧ ¬m.Prime

private theorem progression (j : ℕ) : P (6*j+9) := by
  refine ⟨⟨3*j+4, by omega⟩, ?_⟩
  intro h
  have hd : 3 ∣ 6*j+9 := ⟨2*j+3, by omega⟩
  rcases (Nat.dvd_prime h).mp hd with h | h <;> omega

private theorem infiniteP : (Set.ofPred P).Infinite := by
  have hi : Function.Injective (fun j : ℕ => 6*j+9) := by intro i j h; dsimp at h; omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨j,rfl⟩
  exact progression j

private theorem value_le (i : ℕ) : oddValue i ≤ 6*i+9 :=
  Nat.nth_le_of_strictMonoOn_of_mapsTo (p := P) (fun j => 6*j+9)
    (fun j _ => progression j) (by intro i _ j _ hij; dsimp; omega)

private theorem gap_of_nonprime (i : ℕ) (hp : ¬ (oddValue i + 2).Prime) : a i = 2 := by
  have hi : P (oddValue i) := Nat.nth_mem_of_infinite infiniteP i
  have hj : P (oddValue (i+1)) := Nat.nth_mem_of_infinite infiniteP (i+1)
  have hlt : oddValue i < oddValue (i+1) := Nat.nth_strictMono infiniteP (Nat.lt_succ_self i)
  obtain ⟨k,hk⟩ := hi.1
  obtain ⟨l,hl⟩ := hj.1
  have hu : oddValue (i+1) ≤ oddValue i + 2 := by
    by_contra! h
    have := Nat.le_nth_of_lt_nth_succ (p := P) h ⟨⟨k+1, by omega⟩, hp⟩
    change oddValue i + 2 ≤ oddValue i at this
    omega
  have heq : oddValue (i+1) = oddValue i + 2 := by omega
  have h₀ : isA065090 (oddValue i) := ⟨by omega, Or.inr hi.2⟩
  have h₁ : isA065090 (oddValue i+1) := ⟨by omega, Or.inl ⟨k+1, by omega⟩⟩
  unfold a pos
  rw [heq, Nat.count_succ_eq_succ_count h₁, Nat.count_succ_eq_succ_count h₀]
  omega

private theorem bad_le (N : ℕ) :
    ((range N).filter (fun i => a i ≠ 2)).card ≤ (6*N+11).primeCounting := by
  classical
  let s := (range N).filter (fun i => a i ≠ 2)
  let g := fun i => oddValue i + 2
  have hinj : Function.Injective g := by
    intro i j h
    exact Nat.nth_injective infiniteP (Nat.add_right_cancel h)
  have sub : s.image g ⊆ (6*N+11).primesLE := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨hlt,hbad⟩ := mem_filter.mp hi
    have hiN := mem_range.mp hlt
    exact Nat.mem_primesLE.mpr ⟨by dsimp [g]; have := value_le i; omega,
      by_contra fun hp => hbad (gap_of_nonprime i hp)⟩
  simpa [s, card_image_of_injective _ hinj, Nat.primesLE_card_eq_primeCounting] using card_le_card sub

theorem OMA.solution : type_of% @OMA.S_oeis_a386963.main := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let X := fun N : ℕ => ((6*N+11 : ℕ) : ℝ)
  have hx : Tendsto X atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    exact tendsto_atTop.mpr (fun b => eventually_atTop.mpr ⟨b, fun n hn => by omega⟩)
  let C := Real.log 4 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [eventually_ge_atTop (1:ℕ),
    hx.eventually (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1)),
    (Real.tendsto_log_atTop.comp hx).eventually_gt_atTop (17*C/ε)] with N hN hπ hlog
  change 17*C/ε < Real.log (X N) at hlog
  have hX : X N ≤ 17*(N:ℝ) := by
    dsimp [X]
    push_cast
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hL : 0 < Real.log (X N) := lt_trans (by positivity : 0<17*C/ε) hlog
  have hπ' : ((6*N+11).primeCounting : ℝ) ≤ C * X N / Real.log (X N) := by
    change ((Nat.floor (↑(6*N+11) : ℝ)).primeCounting : ℝ) ≤ _ at hπ
    rw [Nat.floor_natCast] at hπ
    exact hπ
  have hbad := bad_le N
  have hsum := card_filter_add_card_filter_not (s := range N) (fun i => a i = 2)
  rw [card_range] at hsum
  change ((range N).filter (fun i => a i = 2)).card +
    ((range N).filter (fun i => a i ≠ 2)).card = N at hsum
  let good := ((range N).filter (fun i => a i = 2)).card
  have h₁ : (good:ℝ) ≤ N := by exact_mod_cast (show good ≤ N by dsimp [good]; omega)
  have h₂ : (N:ℝ) - good ≤ (6*N+11).primeCounting := by
    have : N ≤ good + (6*N+11).primeCounting := by dsimp [good]; omega
    exact sub_le_iff_le_add.mpr (by exact_mod_cast (by omega : N ≤ (6*N+11).primeCounting + good))
  change dist ((good:ℝ)/N) 1 < ε
  rw [Real.dist_eq, abs_of_nonpos (by rw [sub_nonpos, div_le_iff₀ hNpos]; simpa using h₁)]
  have hprod : 17*C < ε*Real.log (X N) := by have := (div_lt_iff₀ hε).mp hlog; linarith
  have hbound : C*X N/Real.log (X N) < ε*N := by
    apply (div_lt_iff₀ hL).mpr
    calc
      C * X N ≤ C * (17 * N) := mul_le_mul_of_nonneg_left hX hC.le
      _ < ε * N * Real.log (X N) := by
        have := mul_lt_mul_of_pos_right hprod hNpos
        linarith only [this]
  have := h₂.trans_lt (hπ'.trans_lt hbound)
  rw [neg_sub, sub_lt_comm, lt_div_iff₀ hNpos]
  linarith
