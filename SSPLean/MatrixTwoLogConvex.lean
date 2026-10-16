import Mathlib

/-!
# Dimension-corrected log-convexity for nonnegative two-by-two matrices

`conjecture_two_two_by_two` proves that the logarithm of `uᵀ exp(tA) v / t`
is convex on positive times, for every entrywise nonnegative real matrix
and nonnegative endpoint vectors with nonzero pairing. `scalar_pos` proves
strict positivity there. `matrix_curvature_nonneg` also covers the identically
zero case and uses the actual first and second derivatives.

The proof splits the matrix into a scalar part and a traceless part whose
square is a nonnegative scalar multiple of the identity, then uses the
hyperbolic formula for the actual matrix exponential. The zero discriminant
is treated separately by the nilpotent formula.
-/

open scoped Matrix.Norms.Operator
open Matrix NormedSpace

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace SSP.MatrixTwo

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

noncomputable section

local instance : AddCommGroup Mat := Matrix.linftyOpNormedAddCommGroup.toAddCommGroup
local instance : TopologicalSpace Mat := Matrix.linftyOpNormedAddCommGroup.toUniformSpace.toTopologicalSpace
local instance : Module ℝ Mat := Matrix.linftyOpNormedSpace.toModule
local instance : NormedAddCommGroup Mat := Matrix.linftyOpNormedAddCommGroup
local instance : SeminormedAddCommGroup Mat := Matrix.linftyOpSeminormedAddCommGroup
local instance : NormedSpace ℝ Mat := Matrix.linftyOpNormedSpace

noncomputable def curvature (t f f1 f2 : ℝ) : ℝ :=
  t^2 * (f*f2-f1^2)+f^2

theorem curvature_exp_shift (m t f f1 f2 : ℝ) :
    curvature t (Real.exp (m*t)*f)
      (Real.exp (m*t)*(f1+m*f))
      (Real.exp (m*t)*(f2+2*m*f1+m^2*f)) =
    Real.exp (m*t)^2 * curvature t f f1 f2 := by
  unfold curvature
  ring

theorem hyperbolic_curvature {C D x : ℝ}
    (hC : 0 ≤ C) (hD : -C ≤ D) (hx : 0 ≤ x) :
    0 ≤ (C*Real.cosh x+D*Real.sinh x)^2+x^2*(C^2-D^2) := by
  have hs := Real.self_le_sinh_iff.mpr hx
  have hs0 := Real.sinh_nonneg_iff.mpr hx
  by_cases hDC : D ≤ C
  · have hsq : 0 ≤ C^2-D^2 := by nlinarith
    exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hsq)
  · have hD0 : 0 ≤ D := le_trans hC (le_of_not_ge hDC)
    have hf : D*x ≤ C*Real.cosh x+D*Real.sinh x := by
      nlinarith [mul_nonneg hC (Real.cosh_pos x).le,
        mul_nonneg hD0 (sub_nonneg.mpr hs)]
    have hDx : 0 ≤ D*x := mul_nonneg hD0 hx
    nlinarith [sq_nonneg (C*x), sq_nonneg
      (C*Real.cosh x+D*Real.sinh x-D*x)]

noncomputable def rightMul (A : Mat) : Mat →L[ℝ] Mat :=
  ⟨{ toFun := fun M => M*A
     map_add' := fun M N => Matrix.add_mul M N A
     map_smul' := fun r M => Matrix.smul_mul r M A },
   (show Mat →ₗ[ℝ] Mat from
      { toFun := fun M => M*A
        map_add' := fun M N => Matrix.add_mul M N A
        map_smul' := fun r M => Matrix.smul_mul r M A }).continuous_of_finiteDimensional⟩

theorem eq_exp_of_ode (A : Mat) (g : ℝ → Mat)
    (hg : ∀ t, HasDerivAt g (g t*A) t) (hzero : g 0 = 1) :
    g = fun t => NormedSpace.exp (t • A) := by
  apply ODE_solution_unique_univ (K := ‖rightMul A‖₊)
    (s := fun _ => Set.univ) (v := fun _ => rightMul A) (t₀ := 0)
  · intro t
    exact (rightMul A).lipschitz.lipschitzOnWith
  · intro t
    exact ⟨hg t, Set.mem_univ _⟩
  · intro t
    exact ⟨hasDerivAt_exp_smul_const (𝕂 := ℝ) A t, Set.mem_univ _⟩
  · simpa using hzero

theorem exp_formula (A B : Mat) (m k : ℝ) (hk : k ≠ 0)
    (hA : A = m • (1 : Mat)+B) (hB : B*B = k^2 • (1 : Mat)) (t : ℝ) :
    NormedSpace.exp (t • A) =
      Real.exp (m*t) • (Real.cosh (k*t) • (1 : Mat)+
        (Real.sinh (k*t)/k) • B) := by
  let g : ℝ → Mat := fun t =>
    Real.exp (m*t) • (Real.cosh (k*t) • (1 : Mat)+(Real.sinh (k*t)/k) • B)
  have hg : ∀ t, HasDerivAt g (g t*A) t := by
    intro t
    have hc := (Real.hasDerivAt_cosh (k*t)).comp t ((hasDerivAt_id t).const_mul k)
    have hs := ((Real.hasDerivAt_sinh (k*t)).comp t
      ((hasDerivAt_id t).const_mul k)).div_const k
    have he := (Real.hasDerivAt_exp (m*t)).comp t ((hasDerivAt_id t).const_mul m)
    have hd := he.smul ((hc.smul_const (1 : Mat)).add (hs.smul_const B))
    convert hd using 1 <;> try rfl
    rw [hA]
    simp only [g, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hB, smul_add, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Pi.add_apply, Function.comp_apply]
    field_simp [hk]
    ring
  have h := congrFun (eq_exp_of_ode A g hg (by simp [g])) t
  exact h.symm

theorem exp_formula_zero (A B : Mat) (m : ℝ)
    (hA : A = m • (1 : Mat)+B) (hB : B*B = 0) (t : ℝ) :
    NormedSpace.exp (t • A) = Real.exp (m*t) • ((1 : Mat)+t • B) := by
  let g : ℝ → Mat := fun t => Real.exp (m*t) • ((1 : Mat)+t • B)
  have hg : ∀ t, HasDerivAt g (g t*A) t := by
    intro t
    have he := (Real.hasDerivAt_exp (m*t)).comp t ((hasDerivAt_id t).const_mul m)
    have hd := he.smul ((hasDerivAt_const t (1 : Mat)).add
      ((hasDerivAt_id t).smul_const B))
    convert hd using 1 <;> try rfl
    rw [hA]
    simp only [g, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hB, smul_add, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Pi.add_apply, Function.comp_apply, id_eq]
    ring
  exact (congrFun (eq_exp_of_ode A g hg (by simp [g])) t).symm

theorem shifted_hyperbolic_curvature (m k C D t : ℝ)
    (hk : 0 ≤ k) (hC : 0 ≤ C) (hD : -C ≤ D) (ht : 0 ≤ t) :
    let f := fun t => Real.exp (m*t)*(C*Real.cosh (k*t)+D*Real.sinh (k*t))
    0 ≤ curvature t (f t) (deriv f t) (deriv (deriv f) t) := by
  let q := fun t => C*Real.cosh (k*t)+D*Real.sinh (k*t)
  let q1 := fun t => k*(C*Real.sinh (k*t)+D*Real.cosh (k*t))
  let f := fun t => Real.exp (m*t)*q t
  let f1 := fun t => Real.exp (m*t)*(q1 t+m*q t)
  have hq : ∀ t, HasDerivAt q (q1 t) t := by
    intro t
    convert (((Real.hasDerivAt_cosh (k*t)).comp t
      ((hasDerivAt_id t).const_mul k)).const_mul C).add
      (((Real.hasDerivAt_sinh (k*t)).comp t
      ((hasDerivAt_id t).const_mul k)).const_mul D) using 1 <;> (first | rfl | (dsimp [q, q1]; ring))
  have hq1 : ∀ t, HasDerivAt q1 (k^2*q t) t := by
    intro t
    convert ((((Real.hasDerivAt_sinh (k*t)).comp t
      ((hasDerivAt_id t).const_mul k)).const_mul C).add
      (((Real.hasDerivAt_cosh (k*t)).comp t
      ((hasDerivAt_id t).const_mul k)).const_mul D)).const_mul k using 1 <;> (first | rfl | (dsimp [q, q1]; ring))
  have hf : ∀ t, HasDerivAt f (f1 t) t := by
    intro t
    convert ((Real.hasDerivAt_exp (m*t)).comp t
      ((hasDerivAt_id t).const_mul m)).mul (hq t) using 1 <;> (first | rfl | (dsimp [f, f1]; ring))
  have hf1 : HasDerivAt f1
      (Real.exp (m*t)*(k^2*q t+2*m*q1 t+m^2*q t)) t := by
    convert ((Real.hasDerivAt_exp (m*t)).comp t
      ((hasDerivAt_id t).const_mul m)).mul ((hq1 t).add ((hq t).const_mul m)) using 1 <;> (first | rfl | (dsimp [f1]; ring))
  have hderiv : deriv f = f1 := funext fun t => (hf t).deriv
  change 0 ≤ curvature t (f t) (deriv f t) (deriv (deriv f) t)
  rw [hderiv, hf1.deriv]
  dsimp [f, f1]
  rw [curvature_exp_shift]
  apply mul_nonneg (sq_nonneg _)
  have hc := Real.cosh_sq_sub_sinh_sq (k*t)
  have hid : curvature t (q t) (q1 t) (k^2*q t) =
      (C*Real.cosh (k*t)+D*Real.sinh (k*t))^2+(k*t)^2*(C^2-D^2) := by
    dsimp [curvature, q, q1]
    linear_combination t^2*k^2*(C^2-D^2)*hc
  rw [hid]
  exact hyperbolic_curvature hC hD (mul_nonneg hk ht)

noncomputable def scalar (A : Mat) (u v : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  dotProduct u ((NormedSpace.exp (t • A)).mulVec v)

theorem scalar_exp_formula (A B : Mat) (u v : Fin 2 → ℝ) (m k : ℝ)
    (hk : k ≠ 0) (hA : A = m • (1 : Mat)+B) (hB : B*B = k^2 • (1 : Mat)) :
    scalar A u v = fun t => Real.exp (m*t)*
      (dotProduct u v*Real.cosh (k*t)+
        (dotProduct u (B.mulVec v)/k)*Real.sinh (k*t)) := by
  funext t
  rw [scalar, exp_formula A B m k hk hA hB]
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    dotProduct_smul, dotProduct_add, smul_eq_mul]
  ring

theorem scalar_exp_formula_zero (A B : Mat) (u v : Fin 2 → ℝ) (m : ℝ)
    (hA : A = m • (1 : Mat)+B) (hB : B*B = 0) :
    scalar A u v = fun t => Real.exp (m*t)*
      (dotProduct u v+t*dotProduct u (B.mulVec v)) := by
  funext t
  rw [scalar, exp_formula_zero A B m hA hB]
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    dotProduct_smul, dotProduct_add, smul_eq_mul]

theorem shifted_affine_curvature (m C D t : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ht : 0 ≤ t) :
    let f := fun t => Real.exp (m*t)*(C+t*D)
    0 ≤ curvature t (f t) (deriv f t) (deriv (deriv f) t) := by
  let f := fun t => Real.exp (m*t)*(C+t*D)
  let f1 := fun t => Real.exp (m*t)*(D+m*(C+t*D))
  have hf : ∀ t, HasDerivAt f (f1 t) t := by
    intro t
    convert ((Real.hasDerivAt_exp (m*t)).comp t
      ((hasDerivAt_id t).const_mul m)).mul
      ((hasDerivAt_const t C).add ((hasDerivAt_id t).mul_const D)) using 1 <;> (first | rfl | (dsimp [f, f1]; ring))
  have hf1 : HasDerivAt f1 (Real.exp (m*t)*(2*m*D+m^2*(C+t*D))) t := by
    convert ((Real.hasDerivAt_exp (m*t)).comp t
      ((hasDerivAt_id t).const_mul m)).mul
      ((hasDerivAt_const t D).add
        (((hasDerivAt_const t C).add ((hasDerivAt_id t).mul_const D)).const_mul m)) using 1 <;> (first | rfl | (dsimp [f1]; ring))
  have hderiv : deriv f = f1 := funext fun t => (hf t).deriv
  change 0 ≤ curvature t (f t) (deriv f t) (deriv (deriv f) t)
  rw [hderiv, hf1.deriv]
  dsimp [f, f1]
  have hid : curvature t (Real.exp (m*t)*(C+t*D))
      (Real.exp (m*t)*(D+m*(C+t*D)))
      (Real.exp (m*t)*(2*m*D+m^2*(C+t*D))) =
      Real.exp (m*t)^2*(C^2+2*C*t*D) := by unfold curvature; ring
  rw [hid]
  positivity

/-- Every scalar matrix-exponential pairing has one of these two explicit forms. -/
theorem scalar_normal_form (A : Mat) (u v : Fin 2 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    (∃ m C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      scalar A u v = fun t => Real.exp (m*t)*(C+t*D)) ∨
    (∃ m k C D : ℝ, 0 < k ∧ 0 ≤ C ∧ -C ≤ D ∧
      scalar A u v = fun t => Real.exp (m*t)*
        (C*Real.cosh (k*t)+D*Real.sinh (k*t))) := by
  let m := (A 0 0+A 1 1)/2
  let r := (A 0 0-A 1 1)/2
  let k := Real.sqrt (r^2+A 0 1*A 1 0)
  let B : Mat := !![r, A 0 1; A 1 0, -r]
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hk2 : k^2 = r^2+A 0 1*A 1 0 := Real.sq_sqrt
    (add_nonneg (sq_nonneg _) (mul_nonneg (hA 0 1) (hA 1 0)))
  have hsplit : A = m • (1 : Mat)+B := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B, m, r] <;> ring
  have hBsquare : B*B = k^2 • (1 : Mat) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.mul_apply, Fin.sum_univ_two, hk2] <;> ring
  have hC : 0 ≤ dotProduct u v := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hu i) (hv i)
  by_cases hk : k = 0
  · have hr : r = 0 := by
      have hp := mul_nonneg (hA 0 1) (hA 1 0)
      rw [hk] at hk2
      nlinarith [sq_nonneg r]
    have hB0 : B*B = 0 := by simpa [hk] using hBsquare
    have hD : 0 ≤ dotProduct u (B.mulVec v) := by
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      simp [B, hr]
      exact add_nonneg (mul_nonneg (hu 0) (mul_nonneg (hA 0 1) (hv 1)))
        (mul_nonneg (hu 1) (mul_nonneg (hA 1 0) (hv 0)))
    exact Or.inl ⟨m, dotProduct u v, dotProduct u (B.mulVec v), hC, hD,
      scalar_exp_formula_zero A B u v m hsplit hB0⟩
  · have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hk)
    have hrbound : -k ≤ r ∧ r ≤ k := by
      have hp := mul_nonneg (hA 0 1) (hA 1 0)
      constructor <;> nlinarith [sq_nonneg (k+r), sq_nonneg (k-r)]
    have hD : -dotProduct u v ≤ dotProduct u (B.mulVec v)/k := by
      apply (le_div_iff₀ hkpos).mpr
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      simp [B]
      have h00 := mul_nonneg (mul_nonneg (hu 0) (hv 0)) (by linarith : 0 ≤ r+k)
      have h11 := mul_nonneg (mul_nonneg (hu 1) (hv 1)) (by linarith : 0 ≤ k-r)
      have h01 := mul_nonneg (mul_nonneg (hu 0) (hA 0 1)) (hv 1)
      have h10 := mul_nonneg (mul_nonneg (hu 1) (hA 1 0)) (hv 0)
      nlinarith
    exact Or.inr ⟨m, k, dotProduct u v, dotProduct u (B.mulVec v)/k,
      hkpos, hC, hD, scalar_exp_formula A B u v m k hk hsplit hBsquare⟩

/-- The dimension-two corrected curvature inequality, including the zero pairing. -/
theorem matrix_curvature_nonneg (A : Mat) (u v : Fin 2 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ curvature t (scalar A u v t) (deriv (scalar A u v) t)
      (deriv (deriv (scalar A u v)) t) := by
  rcases scalar_normal_form A u v hA hu hv with
    ⟨m, C, D, hC, hD, hf⟩ | ⟨m, k, C, D, hk, hC, hD, hf⟩
  · rw [hf]
    exact shifted_affine_curvature m C D t hC hD ht
  · rw [hf]
    exact shifted_hyperbolic_curvature m k C D t hk.le hC hD ht

/-- Smoothness is obtained from the explicit formula, including repeated eigenvalues. -/
theorem scalar_contDiff (A : Mat) (u v : Fin 2 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    ContDiff ℝ 2 (scalar A u v) := by
  rcases scalar_normal_form A u v hA hu hv with
    ⟨m, C, D, hC, hD, hf⟩ | ⟨m, k, C, D, hk, hC, hD, hf⟩
  · rw [hf]
    fun_prop
  · rw [hf]
    fun_prop

/-- A nonzero pairing is strictly positive at every positive time. -/
theorem scalar_pos (A : Mat) (u v : Fin 2 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hne : scalar A u v ≠ 0) (t : ℝ) (ht : 0 < t) :
    0 < scalar A u v t := by
  rcases scalar_normal_form A u v hA hu hv with
    ⟨m, C, D, hC, hD, hf⟩ | ⟨m, k, C, D, hk, hC, hD, hf⟩
  · have hcoeff : C ≠ 0 ∨ D ≠ 0 := by
      by_contra h
      push Not at h
      apply hne
      rw [hf, h.1, h.2]
      ext x
      simp
    rw [hf]
    apply mul_pos (Real.exp_pos _)
    rcases hcoeff with hc | hd
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hC hc.symm) (mul_nonneg ht.le hD)
    · exact add_pos_of_nonneg_of_pos hC (mul_pos ht (lt_of_le_of_ne hD hd.symm))
  · have hCD : 0 ≤ C+D := by linarith
    have hcoeff : C ≠ 0 ∨ C+D ≠ 0 := by
      by_contra h
      push Not at h
      have hd : D = 0 := by linarith [h.1, h.2]
      apply hne
      rw [hf, h.1, hd]
      ext x
      simp
    rw [hf]
    apply mul_pos (Real.exp_pos _)
    have hid : C*Real.cosh (k*t)+D*Real.sinh (k*t) =
        C*Real.exp (-(k*t))+(C+D)*Real.sinh (k*t) := by
      rw [Real.cosh_eq, Real.sinh_eq]
      ring
    rw [hid]
    have hs := Real.sinh_pos_iff.mpr (mul_pos hk ht)
    rcases hcoeff with hc | hcd
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne hC hc.symm) (Real.exp_pos _)) (mul_nonneg hCD hs.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hC (Real.exp_pos _).le)
        (mul_pos (lt_of_le_of_ne hCD hcd.symm) hs)

/-- Corrected curvature implies convexity of the logarithm after division by time. -/
theorem log_div_convex_of_curvature (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hpos : ∀ t, 0 < t → 0 < f t)
    (hcurv : ∀ t, 0 < t → 0 ≤ curvature t (f t) (deriv f t) (deriv (deriv f) t)) :
    ConvexOn ℝ (Set.Ioi 0) (fun t => Real.log (f t/t)) := by
  let g := fun t => Real.log (f t)-Real.log t
  let g1 := fun t => deriv f t/f t-1/t
  let g2 := fun t => (deriv (deriv f) t*f t-(deriv f t)^2)/(f t)^2+1/t^2
  have hfd := hf.differentiable (by norm_num)
  have hfd1 := hf.differentiable_deriv_two
  have hg : ∀ t, 0 < t → HasDerivAt g (g1 t) t := by
    intro t ht
    exact ((hfd t).hasDerivAt.log (hpos t ht).ne').sub
      ((hasDerivAt_id t).log ht.ne')
  have hg1 : ∀ t, 0 < t → HasDerivAt g1 (g2 t) t := by
    intro t ht
    have hd := ((hfd1 t).hasDerivAt.div (hfd t).hasDerivAt (hpos t ht).ne').sub
      ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht.ne')
    convert hd using 1 <;> (first | rfl | (dsimp [g1, g2]; ring))
  have hg2 : ∀ t, 0 < t → 0 ≤ g2 t := by
    intro t ht
    have hft := (hpos t ht).ne'
    have hid : g2 t = curvature t (f t) (deriv f t) (deriv (deriv f) t)/
        (t^2*(f t)^2) := by
      dsimp [g2, curvature]
      field_simp
    rw [hid]
    exact div_nonneg (hcurv t ht) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hconv : ConvexOn ℝ (Set.Ioi 0) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi (0 : ℝ))
      (f' := g1) (f'' := g2)
    · intro t ht
      exact (hg t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hg t (by simpa only [interior_Ioi, Set.mem_Ioi] using ht)).hasDerivWithinAt
    · intro t ht
      exact (hg1 t (by simpa only [interior_Ioi, Set.mem_Ioi] using ht)).hasDerivWithinAt
    · intro t ht
      exact hg2 t (by simpa only [interior_Ioi, Set.mem_Ioi] using ht)
  apply hconv.congr
  intro t ht
  exact (Real.log_div (hpos t ht).ne' ht.ne').symm

/-- Conjecture 2 in dimension two: the logarithm of `uᵀ exp(tA) v / t` is convex
on positive times for every nonnegative matrix and nonnegative endpoint vectors,
provided the pairing is not identically zero. -/
theorem conjecture_two_two_by_two (A : Mat) (u v : Fin 2 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hne : scalar A u v ≠ 0) :
    ConvexOn ℝ (Set.Ioi 0) (fun t => Real.log (scalar A u v t/t)) := by
  exact log_div_convex_of_curvature (scalar A u v) (scalar_contDiff A u v hA hu hv)
    (scalar_pos A u v hA hu hv hne)
    (fun t ht => matrix_curvature_nonneg A u v hA hu hv t ht.le)

end

end SSP.MatrixTwo
