import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Tactic

/-! # Uniqueness for scalar constant-coefficient cubic ODEs -/

set_option autoImplicit false

namespace SSP.CubicODE

abbrev State := Fin 3 → ℝ

noncomputable def state (f f1 f2 : ℝ → ℝ) (t : ℝ) : State :=
  ![f t, f1 t, f2 t]

noncomputable def fieldLinearMap (c0 c1 c2 : ℝ) : State →ₗ[ℝ] State where
  toFun x := ![x 1, x 2, c0 * x 0 + c1 * x 1 + c2 * x 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
    all_goals ring
  map_smul' q x := by
    ext i
    fin_cases i <;> simp
    all_goals ring

noncomputable def field (c0 c1 c2 : ℝ) : State →L[ℝ] State :=
  ⟨fieldLinearMap c0 c1 c2,
    (fieldLinearMap c0 c1 c2).continuous_of_finiteDimensional⟩

theorem state_hasDerivAt
    {c0 c1 c2 : ℝ} {f f1 f2 : ℝ → ℝ} {t : ℝ}
    (h0 : HasDerivAt f (f1 t) t)
    (h1 : HasDerivAt f1 (f2 t) t)
    (h2 : HasDerivAt f2
      (c0 * f t + c1 * f1 t + c2 * f2 t) t) :
    HasDerivAt (state f f1 f2)
      (field c0 c1 c2 (state f f1 f2 t)) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [state, field, fieldLinearMap] using h0
  · simpa [state, field, fieldLinearMap] using h1
  · simpa [state, field, fieldLinearMap] using h2

/-- Two global three-times differentiable solutions of the same scalar cubic
ODE with the same value and first two derivatives at one point coincide. -/
theorem eq_of_cubic_ode
    {c0 c1 c2 t0 : ℝ}
    {f f1 f2 g g1 g2 : ℝ → ℝ}
    (hf0 : ∀ t, HasDerivAt f (f1 t) t)
    (hf1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hf2 : ∀ t, HasDerivAt f2
      (c0 * f t + c1 * f1 t + c2 * f2 t) t)
    (hg0 : ∀ t, HasDerivAt g (g1 t) t)
    (hg1 : ∀ t, HasDerivAt g1 (g2 t) t)
    (hg2 : ∀ t, HasDerivAt g2
      (c0 * g t + c1 * g1 t + c2 * g2 t) t)
    (hinit0 : f t0 = g t0) (hinit1 : f1 t0 = g1 t0)
    (hinit2 : f2 t0 = g2 t0) :
    f = g := by
  let L := field c0 c1 c2
  have hstate : state f f1 f2 = state g g1 g2 := by
    apply ODE_solution_unique_univ
      (K := ‖L‖₊) (s := fun _ => Set.univ)
      (v := fun _ => L) (t₀ := t0)
    · intro t
      exact L.lipschitz.lipschitzOnWith
    · intro t
      refine ⟨?_, Set.mem_univ _⟩
      exact state_hasDerivAt (hf0 t) (hf1 t) (hf2 t)
    · intro t
      refine ⟨?_, Set.mem_univ _⟩
      exact state_hasDerivAt (hg0 t) (hg1 t) (hg2 t)
    · ext i
      fin_cases i <;> simp [state, hinit0, hinit1, hinit2]
  funext t
  have ht := congrFun hstate t
  exact congrFun ht 0

end SSP.CubicODE
