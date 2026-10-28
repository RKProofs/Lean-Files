import SSPLean.BlockTriangularMoments
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Four-state moment inequalities for sums of two two-state components

The matrices `B ⊗ I + I ⊗ C` can be irreducible and contain multiple cycles.
The exponential factors as a Kronecker product. The two-state theorem proves
entrywise log-convexity after division by `t²`, and hence after division by `t³`.
The existing analytic reduction then proves every moment inequality, with an atom.
This is a concrete subclass, not the conjecture for arbitrary four-state matrices.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 12
open scoped Matrix.Norms.Operator Kronecker
open Matrix Set NormedSpace

namespace SSP.LogConvexIntegral

/-- Products add the correction exponents; identically zero factors are allowed. -/
theorem PositiveLogConvex.mul {p q : ℕ} {f g : ℝ → ℝ}
    (hf : PositiveLogConvex p f) (hg : PositiveLogConvex q g) :
    PositiveLogConvex (p + q) (fun t => f t * g t) := by
  rcases hf with hf | ⟨hfp, hfc⟩
  · left; ext t; simp [hf]
  rcases hg with hg | ⟨hgp, hgc⟩
  · left; ext t; simp [hg]
  right
  refine ⟨fun t ht => mul_pos (hfp t ht) (hgp t ht), ?_⟩
  apply (hfc.add hgc).congr
  intro t ht
  simp only [Pi.add_apply]
  rw [← Real.log_mul (div_pos (hfp t ht) (pow_pos ht _)).ne'
    (div_pos (hgp t ht) (pow_pos ht _)).ne', ← mul_div_mul_comm, ← pow_add]

end SSP.LogConvexIntegral

namespace SSP.TensorSum
open SSP.BlockTriangular SSP.MatrixMomentReduction SSP.LogConvexIntegral

abbrev Mat (n : Type*) := Matrix n n ℝ

noncomputable local instance (n : Type*) [Fintype n] : AddCommGroup (Mat n) :=
  Matrix.linftyOpNormedAddCommGroup.toAddCommGroup
noncomputable local instance (n : Type*) [Fintype n] : TopologicalSpace (Mat n) :=
  Matrix.linftyOpNormedAddCommGroup.toUniformSpace.toTopologicalSpace
noncomputable local instance (n : Type*) [Fintype n] : Module ℝ (Mat n) :=
  Matrix.linftyOpNormedSpace.toModule
noncomputable local instance (n : Type*) [Fintype n] : NormedAddCommGroup (Mat n) :=
  Matrix.linftyOpNormedAddCommGroup
noncomputable local instance (n : Type*) [Fintype n] : SeminormedAddCommGroup (Mat n) :=
  Matrix.linftyOpSeminormedAddCommGroup
noncomputable local instance (n : Type*) [Fintype n] : NormedSpace ℝ (Mat n) :=
  Matrix.linftyOpNormedSpace

variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def leftHom : Mat n →+* Mat (n × m) where
  toFun B := B ⊗ₖ (1 : Mat m)
  map_one' := one_kronecker_one
  map_mul' B E := by rw [← mul_kronecker_mul]; simp
  map_zero' := zero_kronecker _
  map_add' B E := add_kronecker B E _

def rightHom : Mat m →+* Mat (n × m) where
  toFun C := (1 : Mat n) ⊗ₖ C
  map_one' := one_kronecker_one
  map_mul' C E := by rw [← mul_kronecker_mul]; simp
  map_zero' := kronecker_zero _
  map_add' C E := kronecker_add _ C E

theorem exp_kronecker_one (B : Mat n) :
    NormedSpace.exp (B ⊗ₖ (1 : Mat m)) =
      NormedSpace.exp B ⊗ₖ (1 : Mat m) := by
  let L : Mat n →ₗ[ℝ] Mat (n × m) :=
    (Matrix.kroneckerBilinear (R := ℝ) (α := ℝ)).flip (1 : Mat m)
  have hc : Continuous (leftHom (n := n) (m := m)) :=
    L.continuous_of_finiteDimensional
  exact (NormedSpace.map_exp (leftHom (n := n) (m := m)) hc B).symm

theorem exp_one_kronecker (C : Mat m) :
    NormedSpace.exp ((1 : Mat n) ⊗ₖ C) =
      (1 : Mat n) ⊗ₖ NormedSpace.exp C := by
  let L : Mat m →ₗ[ℝ] Mat (n × m) :=
    Matrix.kroneckerBilinear (R := ℝ) (α := ℝ) (1 : Mat n)
  have hc : Continuous (rightHom (n := n) (m := m)) :=
    L.continuous_of_finiteDimensional
  exact (NormedSpace.map_exp (rightHom (n := n) (m := m)) hc C).symm

/-- Factorization of the actual matrix exponential, not an assumed identity. -/
theorem exp_kroneckerSum (B : Mat n) (C : Mat m) (t : ℝ) :
    NormedSpace.exp (t • (B ⊗ₖ (1 : Mat m) + (1 : Mat n) ⊗ₖ C)) =
      NormedSpace.exp (t • B) ⊗ₖ NormedSpace.exp (t • C) := by
  have hcomm : Commute (B ⊗ₖ (1 : Mat m)) ((1 : Mat n) ⊗ₖ C) := by
    change (B ⊗ₖ (1 : Mat m)) * ((1 : Mat n) ⊗ₖ C) =
      ((1 : Mat n) ⊗ₖ C) * (B ⊗ₖ (1 : Mat m))
    rw [← mul_kronecker_mul, ← mul_kronecker_mul]
    simp
  rw [smul_add, NormedSpace.exp_add_of_commute ((hcomm.smul_left t).smul_right t),
    ← smul_kronecker, ← kronecker_smul, exp_kronecker_one, exp_one_kronecker,
    ← mul_kronecker_mul]
  simp

theorem entriesLogConvex_kroneckerSum {p q : ℕ} (B : Mat n) (C : Mat m)
    (hB : EntriesLogConvex B p) (hC : EntriesLogConvex C q) :
    EntriesLogConvex (B ⊗ₖ (1 : Mat m) + (1 : Mat n) ⊗ₖ C) (p + q) := by
  intro i j
  have hid : expEntry (B ⊗ₖ (1 : Mat m) + (1 : Mat n) ⊗ₖ C) i j =
      fun t => expEntry B i.1 j.1 t * expEntry C i.2 j.2 t := by
    funext t
    exact congrArg (fun A : Mat (n × m) => A i j) (exp_kroneckerSum B C t)
  rw [hid]
  exact (hB i.1 j.1).mul (hC i.2 j.2)

/-- The four-state tensor sum in the project's standard `Fin 4` indexing. -/
noncomputable def tensorSum (B C : SSP.MatrixMomentReduction.Mat 2) :
    SSP.MatrixMomentReduction.Mat 4 :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (B ⊗ₖ (1 : SSP.MatrixMomentReduction.Mat 2) +
      (1 : SSP.MatrixMomentReduction.Mat 2) ⊗ₖ C)

theorem tensorSum_nonneg (B C : SSP.MatrixMomentReduction.Mat 2)
    (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) :
    ∀ i j, 0 ≤ tensorSum B C i j := by
  intro i j
  change 0 ≤ B _ _ * (1 : SSP.MatrixMomentReduction.Mat 2) _ _ +
    (1 : SSP.MatrixMomentReduction.Mat 2) _ _ * C _ _
  apply add_nonneg
  · apply mul_nonneg (hB _ _)
    simp only [Matrix.one_apply]; split_ifs <;> norm_num
  · apply mul_nonneg _ (hC _ _)
    simp only [Matrix.one_apply]; split_ifs <;> norm_num

theorem tensorSum_smul (B C : SSP.MatrixMomentReduction.Mat 2) (r : ℝ) :
    tensorSum (r • B) (r • C) = r • tensorSum B C := by
  ext i j
  simp only [tensorSum, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.add_apply, Matrix.smul_apply, kroneckerMap_apply, smul_eq_mul]
  ring

/-- The stronger correction exponent two holds for this four-state family. -/
theorem entriesLogConvex_tensorSum (B C : SSP.MatrixMomentReduction.Mat 2)
    (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) :
    EntriesLogConvex (tensorSum B C) 2 := by
  exact (entriesLogConvex_kroneckerSum B C
    (entriesLogConvex_of_matrixConjecture matrixConjecture_two B hB)
    (entriesLogConvex_of_matrixConjecture matrixConjecture_two C hC)).reindex
      finProdFinEquiv

theorem conjecture_two_tensorSum (B C : SSP.MatrixMomentReduction.Mat 2)
    (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j)
    (u v : Fin 4 → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (pairing (tensorSum B C) u v t / t ^ 3)) :=
  (((entriesLogConvex_tensorSum B C hB hC).pairing u v hu hv).mono
    (by norm_num : 2 ≤ 3)).convex

/-- Every moment index for stable tensor sums, allowing any nonnegative atom. -/
theorem conjecture_one_tensorSum (B C : SSP.MatrixMomentReduction.Mat 2)
    (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j)
    (u v : Fin 4 → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (rate atom : ℝ) (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ ((tensorSum B C).map (algebraMap ℝ ℂ)) < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ((4 + k : ℕ) : ℝ) / ((4 + k - 1 : ℕ) : ℝ) *
        rawMoment (tensorSum B C) u v rate atom k ^ 2 ≤
      rawMoment (tensorSum B C) u v rate atom (k - 1) *
        rawMoment (tensorSum B C) u v rate atom (k + 1) := by
  apply conjecture_one_of_pairing_logConvex (by norm_num) _ _ _ _ _
    (tensorSum_nonneg B C hB hC) hu hv hrate hatom hρ _ k hk
  rw [← tensorSum_smul]
  exact conjecture_two_tensorSum (rate • B) (rate • C)
    (fun i j => mul_nonneg hrate.le (hB i j))
    (fun i j => mul_nonneg hrate.le (hC i j)) u v hu hv

end SSP.TensorSum
