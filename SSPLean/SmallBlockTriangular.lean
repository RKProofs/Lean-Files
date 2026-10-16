import SSPLean.BlockTriangularMoments
import SSPLean.ThreeStateConjectures

/-! Conjectures 2 and 1 for any finite triangular decomposition whose
nonempty diagonal blocks have size at most three. -/
set_option autoImplicit false
open scoped Matrix.Norms.Operator
open Matrix Set

namespace SSP.BlockTriangular
open SSP.MatrixMomentReduction SSP.LogConvexIntegral

noncomputable local instance (s : ℕ) : AddCommGroup (SSP.MatrixMomentReduction.Mat s) := Matrix.linftyOpNormedAddCommGroup.toAddCommGroup
noncomputable local instance (s : ℕ) : TopologicalSpace (SSP.MatrixMomentReduction.Mat s) :=
  Matrix.linftyOpNormedAddCommGroup.toUniformSpace.toTopologicalSpace
noncomputable local instance (s : ℕ) : Module ℝ (SSP.MatrixMomentReduction.Mat s) := Matrix.linftyOpNormedSpace.toModule
noncomputable local instance (s : ℕ) : NormedAddCommGroup (SSP.MatrixMomentReduction.Mat s) := Matrix.linftyOpNormedAddCommGroup
noncomputable local instance (s : ℕ) : SeminormedAddCommGroup (SSP.MatrixMomentReduction.Mat s) := Matrix.linftyOpSeminormedAddCommGroup
noncomputable local instance (s : ℕ) : NormedSpace ℝ (SSP.MatrixMomentReduction.Mat s) := Matrix.linftyOpNormedSpace

/-- The one-state exponential has an affine logarithm. -/
theorem entriesLogConvex_one (A : SSP.MatrixMomentReduction.Mat 1)
    (hA : ∀ i j, 0 ≤ A i j) : EntriesLogConvex A 0 := by
  have hscalar : A = A 0 0 • (1 : SSP.MatrixMomentReduction.Mat 1) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  intro i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  have hid : expEntry A 0 0 = fun t => Real.exp (t*A 0 0) := by
    funext t
    have htA : t • A = (t*A 0 0) • (1 : SSP.MatrixMomentReduction.Mat 1) := by
      calc t • A = t • (A 0 0 • (1 : SSP.MatrixMomentReduction.Mat 1)) :=
          congrArg (fun M => t • M) hscalar
        _ = _ := by rw [smul_smul]
    have he : NormedSpace.exp ((t*A 0 0) • (1 : SSP.MatrixMomentReduction.Mat 1)) =
        Real.exp (t*A 0 0) • (1 : SSP.MatrixMomentReduction.Mat 1) := by
      convert SSP.Semigroup.exp_smul_one 1 (t*A 0 0) using 1; rfl
    unfold expEntry
    rw [htA,he]
    simp
  rw [hid]
  right
  refine ⟨fun _ _ => Real.exp_pos _,?_⟩
  simpa only [pow_zero,div_one,Real.log_exp,smul_eq_mul,mul_comm,id_eq] using
    ConvexOn.smul (hA 0 0) (convexOn_id (convex_Ioi (0 : ℝ)))

theorem entriesLogConvex_small {s : ℕ} (hs : 1 ≤ s) (hs3 : s ≤ 3)
    (A : SSP.MatrixMomentReduction.Mat s) (hA : ∀ i j, 0 ≤ A i j) :
    EntriesLogConvex A (s-1) := by
  have h : s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases h with rfl | rfl | rfl
  · exact entriesLogConvex_one A hA
  · exact entriesLogConvex_of_matrixConjecture matrixConjecture_two A hA
  · exact entriesLogConvex_of_matrixConjecture matrixConjecture_three A hA

/-- A structural certificate of a finite block upper triangular decomposition.
Leaves are arbitrary nonnegative blocks of dimensions 1, 2, or 3; the upper
constructor joins decompositions with an arbitrary nonnegative coupling.
The reindex constructor allows any permutation of the state indices.
This predicate contains no logarithmic-convexity or moment assumption. -/
inductive SmallBlockTriangular : {s : ℕ} → SSP.MatrixMomentReduction.Mat s → Prop
  | small {s : ℕ} (A : SSP.MatrixMomentReduction.Mat s)
      (hs : 1 ≤ s) (hs3 : s ≤ 3) (hA : ∀ i j, 0 ≤ A i j) :
      SmallBlockTriangular A
  | upper {p q : ℕ} {B : SSP.MatrixMomentReduction.Mat p}
      {E : SSP.MatrixMomentReduction.Mat q}
      (C : Matrix (Fin p) (Fin q) ℝ)
      (hB : SmallBlockTriangular B) (hE : SmallBlockTriangular E)
      (hC : ∀ i j, 0 ≤ C i j) : SmallBlockTriangular (upperBlock B C E)
  | reindex {s : ℕ} {A : SSP.MatrixMomentReduction.Mat s}
      (e : Fin s ≃ Fin s) (hA : SmallBlockTriangular A) :
      SmallBlockTriangular (Matrix.reindex e e A)

theorem SmallBlockTriangular.dimension_pos {s : ℕ}
    {A : SSP.MatrixMomentReduction.Mat s} (h : SmallBlockTriangular A) : 1 ≤ s := by
  induction h with
  | small A hs hs3 hA => exact hs
  | upper C hB hE hC ihB ihE => omega
  | reindex e hA ih => exact ih

theorem SmallBlockTriangular.nonneg {s : ℕ}
    {A : SSP.MatrixMomentReduction.Mat s} (h : SmallBlockTriangular A) :
    ∀ i j, 0 ≤ A i j := by
  induction h with
  | small A hs hs3 hA => exact hA
  | upper C hB hE hC ihB ihE => exact upperBlock_nonneg _ C _ ihB hC ihE
  | reindex e hA ih => exact fun i j => ih (e.symm i) (e.symm j)

theorem SmallBlockTriangular.smul {s : ℕ}
    {A : SSP.MatrixMomentReduction.Mat s} (h : SmallBlockTriangular A)
    {r : ℝ} (hr : 0 ≤ r) : SmallBlockTriangular (r • A) := by
  induction h with
  | small A hs hs3 hA =>
    exact .small _ hs hs3 (fun i j => mul_nonneg hr (hA i j))
  | upper C hB hE hC ihB ihE =>
    rw [← upperBlock_smul]
    exact .upper _ ihB ihE (fun i j => mul_nonneg hr (hC i j))
  | reindex e hA ih => exact .reindex e ih

/-- Repeated closure with the total state dimension, independent of block count. -/
theorem SmallBlockTriangular.entriesLogConvex {s : ℕ}
    {A : SSP.MatrixMomentReduction.Mat s} (h : SmallBlockTriangular A) :
    EntriesLogConvex A (s-1) := by
  induction h with
  | small A hs hs3 hA => exact entriesLogConvex_small hs hs3 A hA
  | upper C hB hE hC ihB ihE =>
    exact (entriesLogConvex_fromBlocks hB.dimension_pos hE.dimension_pos
      _ C _ ihB ihE hC).reindex finSumFinEquiv
  | reindex e hA ih => exact ih.reindex e

/-- Conjecture 2 for any nonnegative matrix with the stated decomposition.
The identically zero pairing is included using Lean's `Real.log 0 = 0`. -/
theorem conjecture_two_small_blocks {s : ℕ}
    (A : SSP.MatrixMomentReduction.Mat s) (hA : SmallBlockTriangular A)
    (u v : Fin s → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log
      (SSP.MatrixMomentReduction.pairing A u v t/t^(s-1))) :=
  (hA.entriesLogConvex.pairing u v hu hv).convex

/-- Conjecture 1's moment inequality for every stable uniformized law with
blocks of size at most three, every k ≥ 1, and a nonnegative atom at zero. -/
theorem conjecture_one_small_blocks {s : ℕ}
    (P : SSP.MatrixMomentReduction.Mat s) (hP : SmallBlockTriangular P)
    (u v : Fin s → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (rate atom : ℝ) (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ((s+k : ℕ) : ℝ)/((s+k-1 : ℕ) : ℝ)*rawMoment P u v rate atom k^2 ≤
      rawMoment P u v rate atom (k-1)*rawMoment P u v rate atom (k+1) := by
  exact conjecture_one_of_pairing_logConvex hP.dimension_pos P u v rate atom
    hP.nonneg hu hv hrate hatom hρ
    (conjecture_two_small_blocks _ (hP.smul hrate.le) u v hu hv) k hk

end SSP.BlockTriangular
