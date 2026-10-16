import SSPLean.ThreeStateShiftParameters

/-! # Conjectures 2 and 1 for all nonnegative three-state matrices

The canonical representation is constructed directly from Cayley–Hamilton,
a scalar shift, and nonnegative initial derivative projections.
-/
set_option autoImplicit false
open scoped Matrix.Norms.Operator
open Matrix Set
namespace SSP.ThreeState
noncomputable local instance : AddCommGroup Mat := Matrix.linftyOpNormedAddCommGroup.toAddCommGroup
noncomputable local instance : TopologicalSpace Mat :=
  Matrix.linftyOpNormedAddCommGroup.toUniformSpace.toTopologicalSpace
noncomputable local instance : Module ℝ Mat := Matrix.linftyOpNormedSpace.toModule
noncomputable local instance : NormedAddCommGroup Mat := Matrix.linftyOpNormedAddCommGroup
noncomputable local instance : SeminormedAddCommGroup Mat := Matrix.linftyOpSeminormedAddCommGroup
noncomputable local instance : NormedSpace ℝ Mat := Matrix.linftyOpNormedSpace

open SSP.MatrixMomentReduction SSP.K3Cyclic

theorem pairing_scalar_shift (A : Mat) (u v : Fin 3 → ℝ) (c t : ℝ) :
    pairing (A+c • (1 : Mat)) u v t = Real.exp (c*t)*pairing A u v t := by
  have he : NormedSpace.exp ((c*t) • (1 : Mat)) = Real.exp (c*t) • (1 : Mat) := by
    convert SSP.Semigroup.exp_smul_one 3 (c*t) using 1; rfl
  have hc : Commute (t • A) ((c*t) • (1 : Mat)) :=
    (Commute.one_right (t • A)).smul_right (c*t)
  simp only [pairing]
  rw [show t • (A+c • (1 : Mat)) = t • A+(c*t) • (1 : Mat) by module,
    NormedSpace.exp_add_of_commute hc,he,Matrix.mul_smul,Matrix.mul_one,
    map_smul,smul_eq_mul]

/-- Removing the smallest diagonal keeps all entries nonnegative. -/
theorem exists_zeroDiagonal_shift (A : Mat) (hA : ∀ i j, 0 ≤ A i j) :
    ∃ m : ℝ, (∀ i j, 0 ≤ (A-m • (1 : Mat)) i j) ∧
      ((A-m • (1 : Mat)) 0 0 = 0 ∨ (A-m • (1 : Mat)) 1 1 = 0 ∨
        (A-m • (1 : Mat)) 2 2 = 0) := by
  let m := min (A 0 0) (min (A 1 1) (A 2 2))
  have h0 : m ≤ A 0 0 := min_le_left _ _
  have h1 : m ≤ A 1 1 := (min_le_right _ _).trans (min_le_left _ _)
  have h2 : m ≤ A 2 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨m,?_,?_⟩
  · intro i j
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    split_ifs with hij
    · subst j
      fin_cases i
      · change 0 ≤ A 0 0-m*1; linarith
      · change 0 ≤ A 1 1-m*1; linarith
      · change 0 ≤ A 2 2-m*1; linarith
    · simpa using hA i j
  · have hm : m = A 0 0 ∨ m = A 1 1 ∨ m = A 2 2 := by
      dsimp [m]
      by_cases h : A 0 0 ≤ min (A 1 1) (A 2 2)
      · exact Or.inl (min_eq_left h)
      · rw [min_eq_right (le_of_not_ge h)]
        by_cases h12 : A 1 1 ≤ A 2 2
        · exact Or.inr (Or.inl (min_eq_left h12))
        · exact Or.inr (Or.inr (min_eq_right (le_of_not_ge h12)))
    rcases hm with hm | hm | hm
    · left; simp [hm]
    · right; left; simp [hm]
    · right; right; simp [hm]

/-- Unconditional positive canonical representation for every nonnegative 3×3 pairing. -/
theorem canonicalRepresentation_three (A : Mat) (u v : Fin 3 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    Nonempty (CanonicalPairingRepresentation (pairing A u v)) := by
  obtain ⟨m,hN,hz⟩ := exists_zeroDiagonal_shift A hA
  let N := A-m • (1 : Mat)
  obtain ⟨t,a,b,Q,ht,ha,hab,hQ,hc,hM,hD⟩ := zeroDiagonal_canonical_parameters N hN hz
  let M := N+t • (1 : Mat)
  let R := canonicalRepresentation_of_matrix_cubic M u v hM hu hv ha hab hQ hc hD
  have hAM : A = M+(m-t) • (1 : Mat) := by dsimp [M,N]; module
  refine ⟨{ R with
    shift := m-t
    identity := fun s => by
      rw [hAM,pairing_scalar_shift]
      have hid := R.identity s
      simpa only [R,canonicalRepresentation_of_matrix_cubic,zero_mul,Real.exp_zero,one_mul]
        using congrArg (fun x => Real.exp ((m-t)*s)*x) hid }⟩

end SSP.ThreeState

namespace SSP.MatrixMomentReduction

/-- Every nonnegative 3×3 pairing has the required positive canonical representation. -/
theorem threeStateCanonicalRepresentationTheorem : ThreeStateCanonicalRepresentationTheorem := by
  intro A u v hA hu hv _
  exact SSP.ThreeState.canonicalRepresentation_three A u v hA hu hv

/-- Conjecture 2 for every nonnegative 3×3 matrix and nonnegative pair of vectors. -/
theorem matrixConjecture_three : MatrixConjecture 3 :=
  matrixConjecture_three_of_canonical_representations threeStateCanonicalRepresentationTheorem

/-- Explicit actual matrix-exponential formulation of Conjecture 2. -/
theorem conjecture_two_three_by_three (A : Mat 3) (u v : Fin 3 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hne : pairing A u v ≠ 0) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (pairing A u v t/t^2)) := by
  simpa only [show 3-1 = 2 by omega] using matrixConjecture_three A u v hA hu hv hne

/-- Conjecture 1's inequality for all stable three-state laws, every k ≥ 1,
and an arbitrary nonnegative atom at zero. -/
theorem momentConjecture_three : MomentConjecture 3 :=
  momentConjecture_three_of_canonical_representations threeStateCanonicalRepresentationTheorem

/-- Explicit three-state form of the complete moment inequality. -/
theorem conjecture_one_three_state
    (P : Mat 3) (u v : Fin 3 → ℝ) (rate atom : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ((3+k : ℕ) : ℝ)/((3+k-1 : ℕ) : ℝ)*rawMoment P u v rate atom k^2 ≤
      rawMoment P u v rate atom (k-1)*rawMoment P u v rate atom (k+1) :=
  momentConjecture_three P u v rate atom hP hu hv hrate hatom hρ k hk

end SSP.MatrixMomentReduction
