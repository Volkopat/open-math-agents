import OMAStatements.S_mo_244984

section
open Real Finset OMA.S_mo_244984

lemma mo_per_sum (g : ℕ → ℝ) (n : ℕ) (hg : ∀ i, g (i+n) = g i) (j : ℕ) :
    ∑ i ∈ range n, g (i+j) = ∑ i ∈ range n, g i := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : ∑ i ∈ range n, g (i + (j+1)) = ∑ i ∈ range n, g ((i+1) + j) := by
      apply sum_congr rfl; intro i _; congr 1; ring
    have h2 := sum_range_succ' (fun i => g (i + j)) n
    have h3 := sum_range_succ (fun i => g (i + j)) n
    have h4 : g (n + j) = g (0 + j) := by
      rw [show n + j = j + n by ring, hg]; simp
    rw [h1]
    linarith

lemma mo_path (n : ℕ) (hn : 3 ≤ n) (y : ℕ → ℝ) (h0 : y 0 = 0) (hn' : y n = 0) :
    ∑ k ∈ range n, y k * y (k+1) ≤ cos (π/n) * ∑ k ∈ range n, y k ^ 2 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set c := cos (π/n) with hc
  set s : ℕ → ℝ := fun k => sin (k*π/n) with hs
  have hrec : ∀ m, s (m+2) + s m = 2*c*s (m+1) := by
    intro m
    simp only [hs, hc]
    have e1 : ((m+2:ℕ):ℝ)*π/n = ((m+1:ℕ):ℝ)*π/n + π/n := by
      push_cast; field_simp; ring
    have e2 : ((m:ℕ):ℝ)*π/n = ((m+1:ℕ):ℝ)*π/n - π/n := by
      push_cast; field_simp; ring
    rw [e1, e2, sin_add, sin_sub]; ring
  have hs0 : s 0 = 0 := by simp [hs]
  have hsn : s n = 0 := by
    simp only [hs]
    rw [show (n:ℝ)*π/n = π by field_simp]; exact sin_pi
  have hspos : ∀ k, 0 < k → k < n → 0 < s k := by
    intro k hk1 hk2
    simp only [hs]
    apply sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hnpos]
      have : (k:ℝ) < n := by exact_mod_cast hk2
      nlinarith [pi_pos]
  set S : ℕ → ℝ := fun m => ∑ k ∈ range m, (c * y k ^ 2 - y k * y (k+1)) with hS
  have key : ∀ m, m + 2 ≤ n → 0 ≤ 2 * s (m+1) * S (m+1) + s m * y (m+1) ^ 2 := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [hS, hs0, h0]
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      have p1 : 0 < s (m+1) := hspos _ (by omega) (by omega)
      have p2 : 0 < s (m+2) := hspos _ (by omega) (by omega)
      have hr := hrec m
      have hSs : S (m+2) = S (m+1) + (c * y (m+1) ^ 2 - y (m+1) * y (m+1+1)) := by
        simp only [hS]; rw [sum_range_succ]
      have e : s (m+1) * (2 * s (m+1+1) * S (m+1+1) + s (m+1) * y (m+1+1) ^ 2)
          = s (m+2) * (2 * s (m+1) * S (m+1) + s m * y (m+1) ^ 2)
            + (s (m+2) * y (m+1) - s (m+1) * y (m+1+1)) ^ 2 := by
        rw [show m+1+1 = m+2 by ring, hSs]
        have : c = (s (m+2) + s m) / (2 * s (m+1)) := by
          field_simp; linarith
        rw [this]
        field_simp
        ring
      have : 0 ≤ s (m+1) * (2 * s (m+1+1) * S (m+1+1) + s (m+1) * y (m+1+1) ^ 2) := by
        rw [e]; positivity
      exact nonneg_of_mul_nonneg_right this p1 |> fun h => by simpa using h
  obtain ⟨N, hN⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  have hy : y (N+2) = 0 := hN ▸ hn'
  have hs2 : s (N+2) = 0 := hN ▸ hsn
  have hk := key N (by omega)
  have hr := hrec N
  have hp : 0 < s (N+1) := hspos _ (by omega) (by omega)
  have hSs : S (N+2) = S (N+1) + (c * y (N+1) ^ 2 - y (N+1) * y (N+2)) := by
    simp only [hS]; rw [sum_range_succ]
  have h2 : 0 ≤ 2 * s (N+1) * S (N+2) := by
    rw [hSs, hy]
    rw [hs2] at hr
    nlinarith
  have h3 : 0 ≤ S (N+2) := by
    by_contra hneg
    rw [not_le] at hneg
    nlinarith
  have hSn : S (N+2) = c * ∑ k ∈ range (N+2), y k ^ 2 - ∑ k ∈ range (N+2), y k * y (k+1) := by
    simp only [hS]; rw [sum_sub_distrib, mul_sum]
  rw [hN]; linarith

lemma mo_tan (a b : ℝ) : tangentDist a (vertex b) = 2 * sin ((a-b)/2) ^ 2 := by
  unfold tangentDist projection vertex
  have h1 := cos_two_mul ((a-b)/2)
  have h2 := sin_sq_add_cos_sq ((a-b)/2)
  rw [show 2*((a-b)/2) = a-b by ring] at h1
  have h3 := cos_sub a b
  simp only
  nlinarith

lemma mo_chord (a b tj : ℝ) :
    chordDist a b (vertex tj) = 2 * sin ((a-tj)/2) * sin ((b-tj)/2) := by
  unfold chordDist projection vertex
  have h1 : (b-a)/2 = (b-tj)/2 - (a-tj)/2 := by ring
  have h2 : (a+b)/2 - tj = (b-tj)/2 + (a-tj)/2 := by ring
  simp only
  rw [h1, cos_sub]
  have h3 : cos tj * cos ((a+b)/2) + sin tj * sin ((a+b)/2) = cos ((b-tj)/2 + (a-tj)/2) := by
    rw [← h2, cos_sub]; ring
  rw [h3, cos_add]; ring

lemma mo_vertex (n : ℕ) (t : ℕ → ℝ) (j : ℕ) :
    cos (π/n) * ∑ i ∈ range n, tangentDist (t i) (vertex (t j))
      - ∑ i ∈ range n, chordDist (t i) (t (i+1)) (vertex (t j))
    = 2 * (cos (π/n) * ∑ i ∈ range n, sin ((t i - t j)/2) ^ 2
      - ∑ i ∈ range n, sin ((t i - t j)/2) * sin ((t (i+1) - t j)/2)) := by
  simp only [mo_tan, mo_chord, mul_assoc, ← mul_sum]
  ring


lemma mo_affine (n : ℕ) (t w : ℕ → ℝ) (hw : ∑ i ∈ range n, w i = 1) :
    cos (π/n) * ∑ i ∈ range n, tangentDist (t i) (point n t w)
      - ∑ i ∈ range n, chordDist (t i) (t (i+1)) (point n t w)
    = ∑ j ∈ range n, w j * (cos (π/n) * ∑ i ∈ range n, tangentDist (t i) (vertex (t j))
      - ∑ i ∈ range n, chordDist (t i) (t (i+1)) (vertex (t j))) := by
  have hp : ∀ a, projection a (point n t w) = ∑ j ∈ range n, w j * projection a (vertex (t j)) := by
    intro a
    unfold projection point vertex
    simp only
    rw [sum_mul, sum_mul, ← sum_add_distrib]
    apply sum_congr rfl; intro i _; ring
  have e1 : ∀ a, tangentDist a (point n t w)
      = ∑ j ∈ range n, w j * tangentDist a (vertex (t j)) := by
    intro a
    unfold tangentDist
    rw [hp]
    simp only [mul_sub, sum_sub_distrib, mul_one, hw]
  have e2 : ∀ a b, chordDist a b (point n t w)
      = ∑ j ∈ range n, w j * chordDist a b (vertex (t j)) := by
    intro a b
    unfold chordDist
    rw [hp]
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hw, one_mul]
  simp only [e1, e2, mul_sub, sum_sub_distrib, mul_sum]
  rw [sum_comm (f := fun i j => cos (π/n) * (w j * tangentDist (t i) (vertex (t j)))),
    sum_comm (f := fun i j => w j * chordDist (t i) (t (i+1)) (vertex (t j)))]
  congr 1
  · apply sum_congr rfl; intro j _; apply sum_congr rfl; intro i _; ring

lemma mo_vertex_nonneg (n : ℕ) (hn : 3 ≤ n) (t : ℕ → ℝ) (ht : ∀ i, t (i+n) = t i + 2*π) (j : ℕ) :
    0 ≤ cos (π/n) * ∑ i ∈ range n, tangentDist (t i) (vertex (t j))
      - ∑ i ∈ range n, chordDist (t i) (t (i+1)) (vertex (t j)) := by
  rw [mo_vertex]
  set u : ℕ → ℝ := fun i => sin ((t i - t j)/2) with hu
  have hper : ∀ i, u (i+n) = - u i := by
    intro i
    simp only [hu]
    rw [ht i, show (t i + 2*π - t j)/2 = (t i - t j)/2 + π by ring, sin_add_pi]
  have g1 : ∀ i, (fun i => u i ^ 2) (i+n) = (fun i => u i ^ 2) i := by
    intro i; simp only [hper]; ring
  have g2 : ∀ i, (fun i => u i * u (i+1)) (i+n) = (fun i => u i * u (i+1)) i := by
    intro i
    simp only
    rw [show i + n + 1 = (i+1) + n by ring, hper, hper]; ring
  have s1 := mo_per_sum (fun i => u i ^ 2) n g1 j
  have s2 := mo_per_sum (fun i => u i * u (i+1)) n g2 j
  have := mo_path n hn (fun k => u (k+j)) (by simp [hu]) (by
    simp only [hu]
    rw [show n + j = j + n by ring, ht j, show (t j + 2*π - t j)/2 = π by ring]; exact sin_pi)
  have e : ∀ k, u (k + 1 + j) = u (k + j + 1) := fun k => by rw [Nat.add_right_comm]
  simp only [e] at this
  simp only [hu] at s1 s2 this ⊢
  rw [s1, s2] at this
  nlinarith

lemma mo_roots (n : ℕ) (hn : 3 ≤ n) (x : ℝ) :
    ∑ i ∈ range n, cos (x + i*(2*π/n)) = 0 ∧ ∑ i ∈ range n, sin (x + i*(2*π/n)) = 0 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set h := 2*π/n with hh
  have hS : 0 < sin (h/2) := by
    apply sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [hh, show 2*π/n/2 = π/n by ring, div_lt_iff₀ hnpos]
      have : (3:ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [pi_pos]
  have hnh : (n:ℝ) * h = 2*π := by rw [hh]; field_simp
  constructor
  · have tel := sum_range_sub (fun i : ℕ => sin (x + i*h - h/2)) n
    have e : ∀ i : ℕ, sin (x + ((i+1:ℕ):ℝ)*h - h/2) - sin (x + i*h - h/2)
        = 2 * sin (h/2) * cos (x + i*h) := by
      intro i
      have a1 : x + ((i+1:ℕ):ℝ)*h - h/2 = (x + i*h) + h/2 := by push_cast; ring
      have a2 : x + i*h - h/2 = (x + i*h) - h/2 := rfl
      rw [a1, a2, sin_add, sin_sub]; ring
    simp only [e] at tel
    rw [← mul_sum] at tel
    have : sin (x + n*h - h/2) = sin (x + ((0:ℕ):ℝ)*h - h/2) := by
      rw [show x + n*h - h/2 = (x + ((0:ℕ):ℝ)*h - h/2) + 2*π by push_cast; rw [← hnh]; ring, sin_add_two_pi]
    rw [this] at tel
    simp only [sub_self] at tel
    have h2 : 2 * sin (h/2) ≠ 0 := by positivity
    exact (mul_eq_zero.mp tel).resolve_left h2
  · have tel := sum_range_sub' (fun i : ℕ => cos (x + i*h - h/2)) n
    have e : ∀ i : ℕ, cos (x + i*h - h/2) - cos (x + ((i+1:ℕ):ℝ)*h - h/2)
        = 2 * sin (h/2) * sin (x + i*h) := by
      intro i
      have a1 : x + ((i+1:ℕ):ℝ)*h - h/2 = (x + i*h) + h/2 := by push_cast; ring
      rw [a1, cos_add, show x + i*h - h/2 = (x + i*h) - h/2 from rfl, cos_sub]; ring
    simp only [e] at tel
    rw [← mul_sum] at tel
    have : cos (x + n*h - h/2) = cos (x + ((0:ℕ):ℝ)*h - h/2) := by
      rw [show x + n*h - h/2 = (x + ((0:ℕ):ℝ)*h - h/2) + 2*π by push_cast; rw [← hnh]; ring, cos_add_two_pi]
    rw [this] at tel
    simp only [sub_self] at tel
    have h2 : 2 * sin (h/2) ≠ 0 := by positivity
    exact (mul_eq_zero.mp tel).resolve_left h2


lemma mo_main (n : ℕ) (t w : ℕ → ℝ) (hn : 3 ≤ n) (ht : ∀ i, t (i+n)=t i+2*π)
    (hw0 : ∀ i < n, 0 ≤ w i) (hw : ∑ i ∈ range n,w i=1) :
    ∑ i ∈ range n, chordDist (t i) (t (i+1)) (point n t w)
      ≤ cos (π/n) * ∑ i ∈ range n, tangentDist (t i) (point n t w) ∧
    ((∀ i, t (i+1)=t i+2*π/n) →
      ∑ i ∈ range n, chordDist (t i) (t (i+1)) (point n t w)
        = cos (π/n) * ∑ i ∈ range n, tangentDist (t i) (point n t w)) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  constructor
  · have h1 := mo_affine n t w hw
    have h2 : 0 ≤ ∑ j ∈ range n, w j * (cos (π/n) * ∑ i ∈ range n, tangentDist (t i) (vertex (t j))
      - ∑ i ∈ range n, chordDist (t i) (t (i+1)) (vertex (t j))) := by
      apply sum_nonneg
      intro j hj
      exact mul_nonneg (hw0 j (mem_range.mp hj)) (mo_vertex_nonneg n hn t ht j)
    linarith
  · intro hs
    have ht0 : ∀ i : ℕ, t i = t 0 + i*(2*π/n) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [hs i, ih]; push_cast; ring
    set P := point n t w with hP
    have hT : ∑ i ∈ range n, tangentDist (t i) P
        = n - (P.1 * ∑ i ∈ range n, cos (t i) + P.2 * ∑ i ∈ range n, sin (t i)) := by
      simp only [tangentDist, projection, sum_sub_distrib, sum_add_distrib, ← mul_sum]
      simp
    have hC : ∑ i ∈ range n, chordDist (t i) (t (i+1)) P
        = n * cos (π/n) - (P.1 * ∑ i ∈ range n, cos ((t i + t (i+1))/2)
            + P.2 * ∑ i ∈ range n, sin ((t i + t (i+1))/2)) := by
      have e : ∀ i, (t (i+1) - t i)/2 = π/n := by
        intro i; rw [hs i]; ring
      simp only [chordDist, projection, e, sum_sub_distrib, sum_add_distrib, ← mul_sum]
      simp
    obtain ⟨r1, r2⟩ := mo_roots n hn (t 0)
    obtain ⟨r3, r4⟩ := mo_roots n hn (t 0 + (π/n))
    have q1 : ∑ i ∈ range n, cos (t i) = 0 := by
      rw [← r1]; apply sum_congr rfl; intro i _; rw [← ht0 i]
    have q2 : ∑ i ∈ range n, sin (t i) = 0 := by
      rw [← r2]; apply sum_congr rfl; intro i _; rw [← ht0 i]
    have e3 : ∀ i : ℕ, (t i + t (i+1))/2 = t 0 + π/n + i*(2*π/n) := by
      intro i; rw [hs i, ht0 i]; ring
    have q3 : ∑ i ∈ range n, cos ((t i + t (i+1))/2) = 0 := by
      rw [← r3]; apply sum_congr rfl; intro i _; rw [e3 i]
    have q4 : ∑ i ∈ range n, sin ((t i + t (i+1))/2) = 0 := by
      rw [← r4]; apply sum_congr rfl; intro i _; rw [e3 i]
    rw [hC, hT, q1, q2, q3, q4]; ring

end

theorem OMA.solution : type_of% @OMA.S_mo_244984.main := by
  intro n t w hn _ ht hw0 hw
  exact mo_main n t w hn ht hw0 hw
