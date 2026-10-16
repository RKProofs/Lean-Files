import SSPLean.BlockTriangularExponential
import SSPLean.LogConvexNonnegative

/-! Dimension-additive closure for nonnegative upper triangular block matrices. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 12
open scoped Matrix.Norms.Operator
open Matrix Set NormedSpace
namespace SSP.BlockTriangular

noncomputable local instance (n : Type*) [Fintype n] : AddCommGroup (Mat n) := Matrix.linftyOpNormedAddCommGroup.toAddCommGroup
noncomputable local instance (n : Type*) [Fintype n] : TopologicalSpace (Mat n) :=
  Matrix.linftyOpNormedAddCommGroup.toUniformSpace.toTopologicalSpace
noncomputable local instance (n : Type*) [Fintype n] : Module ℝ (Mat n) := Matrix.linftyOpNormedSpace.toModule
noncomputable local instance (n : Type*) [Fintype n] : NormedAddCommGroup (Mat n) := Matrix.linftyOpNormedAddCommGroup
noncomputable local instance (n : Type*) [Fintype n] : SeminormedAddCommGroup (Mat n) := Matrix.linftyOpSeminormedAddCommGroup
noncomputable local instance (n : Type*) [Fintype n] : NormedSpace ℝ (Mat n) := Matrix.linftyOpNormedSpace

open SSP.LogConvexIntegral SSP.MatrixMomentReduction

/-- Entrywise form, including zero entries, of the dimension-corrected conjecture. -/
def EntriesLogConvex {n : Type} [Fintype n] [DecidableEq n] (A : Mat n) (p : ℕ) : Prop :=
  ∀ i j, PositiveLogConvex p (expEntry A i j)

variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The entrywise two-block closure, for concrete blocks with the required properties. -/
theorem entriesLogConvex_fromBlocks {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (B : Mat n) (C : Matrix n m ℝ) (E : Mat m)
    (hB : EntriesLogConvex B (p-1)) (hE : EntriesLogConvex E (q-1))
    (hC : ∀ i j, 0 ≤ C i j) :
    EntriesLogConvex (fromBlocks B C 0 E) (p+q-1) := by
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simpa only [show expEntry (fromBlocks B C 0 E) (Sum.inl i) (Sum.inl j) =
          expEntry B i j from funext (block_exp_inl_inl B C E i j)] using
        (hB i j).mono (show p-1 ≤ p+q-1 by omega)
    | inr j =>
      have h := PositiveLogConvex.sum Finset.univ (fun a t => ∑ b,
        C a b*SSP.LogConvexIntegral.convolution (expEntry B i a) (expEntry E b j) t) (by
          intro a _
          apply PositiveLogConvex.sum
          intro b _
          exact ((hB i a).convolution (hE b j)
            (expEntry_continuous B i a) (expEntry_continuous E b j)).const_mul (hC a b))
      have hexp : p-1+(q-1)+1 = p+q-1 := by omega
      rw [hexp] at h
      have hid : expEntry (fromBlocks B C 0 E) (Sum.inl i) (Sum.inr j) =
          fun t => ∑ a, ∑ b, C a b*SSP.LogConvexIntegral.convolution
            (expEntry B i a) (expEntry E b j) t := by
        funext t
        exact block_exp_inl_inr B C E i j t
      simpa only [hid] using h
  | inr i =>
    cases j with
    | inl j =>
      left
      funext t
      exact block_exp_inr_inl B C E i j t
    | inr j =>
      simpa only [show expEntry (fromBlocks B C 0 E) (Sum.inr i) (Sum.inr j) =
          expEntry E i j from funext (block_exp_inr_inr B C E i j)] using
        (hE i j).mono (show q-1 ≤ p+q-1 by omega)

/-- Relabeling matrix indices preserves the actual exponential. -/
theorem expEntry_reindex (e : n ≃ m) (A : Mat n) (i j : m) (t : ℝ) :
    expEntry (Matrix.reindex e e A) i j t = expEntry A (e.symm i) (e.symm j) t := by
  let R := Matrix.reindexAlgEquiv ℝ ℝ e
  have hc : Continuous R := R.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have h := NormedSpace.map_exp R hc (t • A)
  have hs : R (t • A) = t • R A := R.toLinearEquiv.map_smul t A
  rw [hs] at h
  exact (congrArg (fun M : Mat m => M i j) h).symm

theorem EntriesLogConvex.reindex {p : ℕ} {A : Mat n} (h : EntriesLogConvex A p)
    (e : n ≃ m) : EntriesLogConvex (Matrix.reindex e e A) p := by
  intro i j
  have hid := funext (expEntry_reindex e A i j)
  rw [hid]
  exact h _ _

/-- Arbitrary nonnegative endpoint vectors are handled by finite positive sums. -/
theorem EntriesLogConvex.pairing {s p : ℕ} {A : SSP.MatrixMomentReduction.Mat s}
    (h : EntriesLogConvex A p) (u v : Fin s → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    PositiveLogConvex p (SSP.MatrixMomentReduction.pairing A u v) := by
  have hc := PositiveLogConvex.sum Finset.univ
    (fun i t => ∑ j, (u i*v j)*expEntry A i j t) (by
      intro i _
      apply PositiveLogConvex.sum
      intro j _
      exact (h i j).const_mul (mul_nonneg (hu i) (hv j)))
  have hid : SSP.MatrixMomentReduction.pairing A u v =
      fun t => ∑ i, ∑ j, (u i*v j)*expEntry A i j t := by
    funext t
    simp only [SSP.MatrixMomentReduction.pairing,pairingFun_apply,dotProduct,
      Matrix.mulVec,Finset.mul_sum,expEntry]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hid]
  exact hc

theorem entriesLogConvex_of_matrixConjecture {p : ℕ}
    (hconj : MatrixConjecture p) (B : SSP.MatrixMomentReduction.Mat p)
    (hB : ∀ i j, 0 ≤ B i j) : EntriesLogConvex B (p-1) := by
  intro i j
  let u : Fin p → ℝ := Pi.single i 1
  let v : Fin p → ℝ := Pi.single j 1
  have hu : ∀ k, 0 ≤ u k := by intro k; simp [u,Pi.single_apply]; split <;> norm_num
  have hv : ∀ k, 0 ≤ v k := by intro k; simp [v,Pi.single_apply]; split <;> norm_num
  have hid : SSP.MatrixMomentReduction.pairing B u v = expEntry B i j := by
    funext t
    simp [SSP.MatrixMomentReduction.pairing,pairingFun_apply,u,v,
      single_dotProduct,Matrix.mulVec_single,expEntry]
  by_cases hz : SSP.MatrixMomentReduction.pairing B u v = 0
  · left; rw [← hid]; exact hz
  · right
    rw [← hid]
    exact ⟨pairing_pos B u v hB hu hv hz,hconj B u v hB hu hv hz⟩

/-- Upper triangular block matrix in standard `Fin (p+q)` indexing. -/
noncomputable def upperBlock {p q : ℕ}
    (B : SSP.MatrixMomentReduction.Mat p) (C : Matrix (Fin p) (Fin q) ℝ)
    (E : SSP.MatrixMomentReduction.Mat q) : SSP.MatrixMomentReduction.Mat (p+q) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks B C 0 E)

/-- Proposition "Block-triangular closure" from the TeX document. -/
theorem block_triangular_closure {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hconjB : MatrixConjecture p) (hconjE : MatrixConjecture q)
    (B : SSP.MatrixMomentReduction.Mat p) (C : Matrix (Fin p) (Fin q) ℝ)
    (E : SSP.MatrixMomentReduction.Mat q)
    (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) (hE : ∀ i j, 0 ≤ E i j)
    (u v : Fin (p+q) → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log
      (SSP.MatrixMomentReduction.pairing (upperBlock B C E) u v t/t^(p+q-1))) := by
  exact ((entriesLogConvex_fromBlocks hp hq B C E
    (entriesLogConvex_of_matrixConjecture hconjB B hB)
    (entriesLogConvex_of_matrixConjecture hconjE E hE) hC).reindex finSumFinEquiv
      |>.pairing u v hu hv).convex

theorem upperBlock_nonneg {p q : ℕ}
    (B : SSP.MatrixMomentReduction.Mat p) (C : Matrix (Fin p) (Fin q) ℝ)
    (E : SSP.MatrixMomentReduction.Mat q)
    (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) (hE : ∀ i j, 0 ≤ E i j) :
    ∀ i j, 0 ≤ upperBlock B C E i j := by
  intro i j
  change 0 ≤ (fromBlocks B C 0 E) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  cases finSumFinEquiv.symm i with
  | inl i =>
    cases finSumFinEquiv.symm j with
    | inl j => exact hB i j
    | inr j => exact hC i j
  | inr i =>
    cases finSumFinEquiv.symm j with
    | inl j => exact le_rfl
    | inr j => exact hE i j

theorem upperBlock_smul {p q : ℕ}
    (B : SSP.MatrixMomentReduction.Mat p) (C : Matrix (Fin p) (Fin q) ℝ)
    (E : SSP.MatrixMomentReduction.Mat q) (r : ℝ) :
    upperBlock (r • B) (r • C) (r • E) = r • upperBlock B C E := by
  ext i j
  change (fromBlocks (r • B) (r • C) 0 (r • E))
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) =
    r*(fromBlocks B C 0 E) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp

end SSP.BlockTriangular
