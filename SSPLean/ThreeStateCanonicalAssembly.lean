import SSPLean.ThreeStateMomentBridge
import SSPLean.ThreeStatePowerProjection

/-! # Constructing canonical scalar pairings from a matrix cubic

The only entrywise sign needed beyond `M ≥ 0` is `M²-aM ≥ 0`.
The canonical mixture coefficients are constructed from the first three
initial derivatives, and the representation identity follows from cubic ODE
uniqueness.
-/

set_option autoImplicit false
open scoped Matrix.Norms.Operator
open Matrix Set

namespace SSP.ThreeState

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
noncomputable local instance : AddCommGroup Mat := Matrix.linftyOpNormedAddCommGroup.toAddCommGroup
noncomputable local instance : TopologicalSpace Mat :=
  Matrix.linftyOpNormedAddCommGroup.toUniformSpace.toTopologicalSpace
noncomputable local instance : Module ℝ Mat := Matrix.linftyOpNormedSpace.toModule
noncomputable local instance : NormedAddCommGroup Mat := Matrix.linftyOpNormedAddCommGroup
noncomputable local instance : SeminormedAddCommGroup Mat := Matrix.linftyOpSeminormedAddCommGroup
noncomputable local instance : NormedSpace ℝ Mat := Matrix.linftyOpNormedSpace

open SSP.MatrixMomentReduction SSP.K3Cyclic

noncomputable def pairingDerivative (M : Mat) (u v : Fin 3 → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  pairingFun u v (NormedSpace.exp (t • M)*M^n)

theorem pairingDerivative_hasDerivAt (M : Mat) (u v : Fin 3 → ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (pairingDerivative M u v n) (pairingDerivative M u v (n+1) t) t := by
  have hd := (pairingFun u v).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_exp_smul_const (𝕂 := ℝ) M t).mul_const (M^n))
  convert hd using 1 <;> try rfl
  dsimp [pairingDerivative]
  congr 1
  rw [pow_succ']
  simp [mul_assoc]

@[simp] theorem pairingDerivative_zero (M : Mat) (u v : Fin 3 → ℝ) (n : ℕ) :
    pairingDerivative M u v n 0 = pairingFun u v (M^n) := by
  simp [pairingDerivative]

theorem pairingDerivative_cubic (M : Mat) (u v : Fin 3 → ℝ) (a b Q : ℝ)
    (hM : M^3 = (a+b) • M^2-(a*b) • M+Q • (1 : Mat)) (t : ℝ) :
    HasDerivAt (pairingDerivative M u v 2)
      (Q*pairingDerivative M u v 0 t-a*b*pairingDerivative M u v 1 t+
        (a+b)*pairingDerivative M u v 2 t) t := by
  have hd := pairingDerivative_hasDerivAt M u v 2 t
  convert hd using 1; try rfl
  dsimp [pairingDerivative]
  rw [hM]
  simp only [Matrix.mul_add,Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,
    map_add,map_sub,map_smul,smul_eq_mul,pow_one,pow_zero]
  ring

theorem pairing_eq_canonicalMixture (M : Mat) (u v : Fin 3 → ℝ) (a b Q : ℝ)
    (hM : M^3 = (a+b) • M^2-(a*b) • M+Q • (1 : Mat)) :
    pairing M u v = canonicalMixture a b Q 1 1
      (pairingFun u v 1) (pairingFun u v M) (pairingFun u v (M^2-a • M)) := by
  let p0 := pairingFun u v 1
  let p1 := pairingFun u v M
  let p2 := pairingFun u v (M^2-a • M)
  let f := canonicalFirst a b Q 1 1
  let g := canonicalMiddle a b Q 1 1
  let h := canonicalThird a b Q 1 1
  let f1 := canonicalFirstDeriv a b Q 1 1
  let g1 := canonicalMiddleDeriv a b Q 1 1
  let h1 := canonicalThirdDeriv a b Q 1 1
  let f2 := canonicalFirstDeriv2 a b Q 1 1
  let g2 := canonicalMiddleDeriv2 a b Q 1 1
  let h2 := canonicalThirdDeriv2 a b Q 1 1
  have hEq : pairingDerivative M u v 0 = canonicalMixture a b Q 1 1 p0 p1 p2 := by
    apply SSP.CubicODE.eq_of_cubic_ode (c0 := Q) (c1 := -a*b) (c2 := a+b) (t0 := 0)
      (f1 := pairingDerivative M u v 1) (f2 := pairingDerivative M u v 2)
      (g1 := fun t => p0*f1 t+p1*g1 t+p2*h1 t)
      (g2 := fun t => p0*f2 t+p1*g2 t+p2*h2 t)
    · exact pairingDerivative_hasDerivAt M u v 0
    · exact pairingDerivative_hasDerivAt M u v 1
    · intro t
      convert pairingDerivative_cubic M u v a b Q hM t using 1; try rfl
      ring
    · intro t
      exact (((canonicalFirst_hasDerivAt a b Q 1 1 t).const_mul p0).add
        ((canonicalMiddle_hasDerivAt a b Q 1 1 t).const_mul p1) |>.add
        ((canonicalThird_hasDerivAt a b Q 1 1 t).const_mul p2))
    · intro t
      exact (((canonicalFirstDeriv_hasDerivAt a b Q 1 1 t).const_mul p0).add
        ((canonicalMiddleDeriv_hasDerivAt a b Q 1 1 t).const_mul p1) |>.add
        ((canonicalThirdDeriv_hasDerivAt a b Q 1 1 t).const_mul p2))
    · intro t
      have hd := (((canonicalFirstDeriv2_hasDerivAt a b Q 1 1 t).const_mul p0).add
        ((canonicalMiddleDeriv2_hasDerivAt a b Q 1 1 t).const_mul p1) |>.add
        ((canonicalThirdDeriv2_hasDerivAt a b Q 1 1 t).const_mul p2))
      convert hd using 1 <;> try rfl
      simp only [canonicalMixture,f1,g1,h1,f2,g2,h2,mul_one]
      ring
    · simp [canonicalMixture,p0]
    · simp [f1,g1,h1,p1]
    · simp [f2,g2,h2,p1,p2,map_sub,map_smul,smul_eq_mul]
      ring
  have hbase : pairingDerivative M u v 0 = pairing M u v := by
    funext t
    simp [pairingDerivative,pairing]
  rw [hbase] at hEq
  exact hEq

theorem pairingFun_nonneg (M : Mat) (u v : Fin 3 → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    0 ≤ pairingFun u v M := by
  simp only [pairingFun_apply,dotProduct,Matrix.mulVec]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hu i)
    (Finset.sum_nonneg fun j _ => mul_nonneg (hM i j) (hv j))

/-- Construction of the complete positive representation, under matrix-cubic
and entrywise projection conditions. -/
noncomputable def canonicalRepresentation_of_matrix_cubic
    (M : Mat) (u v : Fin 3 → ℝ) {a b Q : ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (ha : 0 ≤ a) (hab : a ≤ b) (hQ : 0 ≤ Q)
    (hcubic : M^3 = (a+b) • M^2-(a*b) • M+Q • (1 : Mat))
    (hD : ∀ i j, 0 ≤ (M^2-a • M) i j) :
    CanonicalPairingRepresentation (pairing M u v) where
  a := a
  b := b
  c := Q
  x2 := 1
  x3 := 1
  pi1 := pairingFun u v 1
  pi2 := pairingFun u v M
  pi3 := pairingFun u v (M^2-a • M)
  shift := 0
  a_nonneg := ha
  ordered := hab
  c_nonneg := hQ
  x2_pos := by norm_num
  x3_pos := by norm_num
  pi1_nonneg := power_pairing_nonneg M u v hM hu hv 0
  pi2_nonneg := pairingFun_nonneg M u v hM hu hv
  pi3_nonneg := pairingFun_nonneg _ u v hD hu hv
  identity := fun t => by
    simp only [zero_mul,Real.exp_zero,one_mul]
    exact congrFun (pairing_eq_canonicalMixture M u v a b Q hcubic) t

end SSP.ThreeState
