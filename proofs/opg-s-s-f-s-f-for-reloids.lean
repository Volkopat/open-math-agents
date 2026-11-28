import OMAStatements.S_opg_s_s_f_s_f_for_reloids

/-!
A countable directed graph has a permanent ray and a family of entrances to
its first vertex. The filter permits the omission of any finite initial
segment of the entrances. At fixed path length, a sufficiently late entrance
can only reach a point of the ray below its own index. After closing under
finite powers, one more composition can take it arbitrarily far along the ray.
-/

namespace RayReloid

open Filter OMA.S_opg_s_s_f_s_f_for_reloids

private inductive Vertex where
  | source (p : ℕ)
  | ray (j : ℕ)

open Vertex

private def spine : Set (Vertex × Vertex) :=
  {e | ∃ j, e = (ray j, ray (j+1))}

private def entrance (p : ℕ) := (source p, ray 0)

private def edges (N : ℕ) : Set (Vertex × Vertex) :=
  {e | e ∈ spine ∨ ∃ p, N ≤ p ∧ e = entrance p}

private def f : Filter (Vertex × Vertex) :=
  principal spine ⊔ map entrance atTop

private theorem edges_mem (N : ℕ) : edges N ∈ f := by
  constructor
  · exact fun _ h => Or.inl h
  · change ∀ᶠ p : ℕ in atTop, entrance p ∈ edges N
    filter_upwards [eventually_ge_atTop N] with p hp using Or.inr ⟨p, hp, rfl⟩

private def paths (N : ℕ) : ℕ → Set (Vertex × Vertex)
  | 0 => {e | e.1 = e.2}
  | n+1 => relComp (edges N) (paths N n)

private theorem paths_mem (N n : ℕ) : paths N n ∈ rldPow f n := by
  induction n with
  | zero => exact mem_principal_self _
  | succ n ih => exact mem_generate_of_mem ⟨_, ih, _, edges_mem N, rfl⟩

private theorem from_source (N n p : ℕ) {v : Vertex} (h : (source p,v) ∈ paths N n) :
    v = source p ∨ ∃ j, v = ray j ∧ N ≤ p ∧ j ≤ n := by
  induction n generalizing v with
  | zero => exact Or.inl (show source p = v from h).symm
  | succ n ih =>
    obtain ⟨mid, prev, step⟩ := h
    rcases ih prev with rfl | ⟨j, rfl, hp, hj⟩
    · rcases step with ⟨k, eq⟩ | ⟨q, hq, eq⟩
      · simp at eq
      · simp [entrance] at eq
        exact Or.inr ⟨0, eq.2, eq.1.symm ▸ hq, Nat.zero_le _⟩
    · rcases step with ⟨k, eq⟩ | ⟨q, _, eq⟩
      · simp at eq
        exact Or.inr ⟨k+1, eq.2, hp, by omega⟩
      · simp [entrance] at eq

private def boundedPairs : Set (Vertex × Vertex) :=
  {e | ∀ p j, e = (source p, ray j) → j ≤ p}

private theorem bounded_mem : boundedPairs ∈ S f := by
  apply mem_iSup.mpr
  intro n
  apply mem_of_superset (paths_mem n n)
  rintro _ h p j rfl
  rcases from_source n n p h with eq | ⟨k, eq, hp, hk⟩
  · cases eq
  · cases eq
    omega

private theorem le_pow_one {A : Type} (g : Filter (A × A)) : g ≤ rldPow g 1 := by
  apply le_generate_iff.mpr
  rintro _ ⟨F, hF, G, hG, rfl⟩
  apply mem_of_superset hG
  intro e he
  exact ⟨e.1, hF (show e.1 = e.1 from rfl), he⟩

private theorem le_closure {A : Type} (g : Filter (A × A)) : g ≤ S g :=
  (le_pow_one g).trans (le_iSup (rldPow g) 1)

private theorem ray_path (n : ℕ) : pure (ray 0, ray n) ≤ rldPow f n := by
  induction n with
  | zero => exact le_principal_iff.mpr rfl
  | succ n ih =>
    have next : pure (ray n, ray (n+1)) ≤ f :=
      (le_principal_iff.mpr (show (ray n, ray (n+1)) ∈ spine from ⟨n, rfl⟩)).trans le_sup_left
    apply le_generate_iff.mpr
    rintro _ ⟨F, hF, G, hG, rfl⟩
    exact ⟨ray n, ih hF, next hG⟩

private def beyond (p : ℕ) := (source p, ray (p+1))

private theorem beyond_comp {g : Filter (Vertex × Vertex)} (hg : S f ≤ g) :
    map beyond atTop ≤ rldComp (S f) g := by
  have incoming : map entrance atTop ≤ g :=
    (show map entrance atTop ≤ f from le_sup_right).trans ((le_closure f).trans hg)
  apply le_generate_iff.mpr
  rintro _ ⟨F, hF, G, hG, rfl⟩
  change ∀ᶠ p : ℕ in atTop, beyond p ∈ relComp G F
  have hin : ∀ᶠ p : ℕ in atTop, entrance p ∈ F := incoming hF
  filter_upwards [hin] with p hp
  exact ⟨ray 0, hp, ((ray_path (p+1)).trans (le_iSup (rldPow f) (p+1))) hG⟩

private theorem beyond_bad : boundedPairs ∉ map beyond atTop := by
  intro h
  obtain ⟨p, hp⟩ := (show ∀ᶠ p : ℕ in atTop, beyond p ∈ boundedPairs from h).exists
  exact Nat.not_succ_le_self p (hp p (p+1) rfl)

/-- The same reloid also answers the composition question, Conjecture 11.38(1). -/
theorem composition_counterexample :
    ∃ (A : Type) (g : Filter (A × A)), rldComp (S g) (S g) ≠ S g := by
  refine ⟨Vertex, f, fun h => beyond_bad ?_⟩
  exact (beyond_comp le_rfl) (h.symm ▸ bounded_mem)

private theorem not_idempotent : S (S f) ≠ S f := by
  intro eq
  have twice : boundedPairs ∈ S (S f) := by rw [eq]; exact bounded_mem
  have two : boundedPairs ∈ rldPow (S f) 2 := mem_iSup.mp twice 2
  exact beyond_bad ((beyond_comp (le_pow_one (S f))) two)

end RayReloid

open OMA.S_opg_s_s_f_s_f_for_reloids RayReloid

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_s_s_f_s_f_for_reloids.main) := by
  intro claim
  exact not_idempotent (claim _ _)
