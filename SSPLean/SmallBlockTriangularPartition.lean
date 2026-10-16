import SSPLean.SmallBlockTriangular

/-! Ordinary block-size lists and zeros below the diagonal imply the
structural certificate, hence both conjectures. -/
set_option autoImplicit false
open Matrix Set
namespace SSP.BlockTriangular
open SSP.MatrixMomentReduction

/-- With consecutive blocks of the listed sizes, every entry below a
diagonal block is zero. The tail is the bottom-right principal submatrix. -/
def UpperTriangularBlocks : (sizes : List ℕ) → SSP.MatrixMomentReduction.Mat sizes.sum → Prop
  | [], _ => True
  | p :: sizes, A =>
      (∀ (i : Fin sizes.sum) (j : Fin p),
        A (Fin.natAdd p i) (Fin.castAdd sizes.sum j) = 0) ∧
      UpperTriangularBlocks sizes (A.submatrix (Fin.natAdd p) (Fin.natAdd p))

/-- A standard upper block triangular matrix with nonempty blocks of size
at most three has a finite structural decomposition. -/
theorem smallBlockTriangular_of_partition (sizes : List ℕ) (hne : sizes ≠ [])
    (hsizes : ∀ p ∈ sizes, 1 ≤ p ∧ p ≤ 3)
    (A : SSP.MatrixMomentReduction.Mat sizes.sum)
    (hA : ∀ i j, 0 ≤ A i j) (htri : UpperTriangularBlocks sizes A) :
    SmallBlockTriangular A := by
  induction sizes with
  | nil => exact (hne rfl).elim
  | cons p sizes ih =>
    have hp := hsizes p List.mem_cons_self
    cases sizes with
    | nil =>
      exact .small A (by simpa using hp.1) (by simpa using hp.2) hA
    | cons q sizes =>
      let tail := q :: sizes
      let B := A.submatrix (Fin.castAdd tail.sum) (Fin.castAdd tail.sum)
      let C := A.submatrix (Fin.castAdd tail.sum) (Fin.natAdd p)
      let E := A.submatrix (Fin.natAdd p) (Fin.natAdd p)
      have hB : SmallBlockTriangular B := .small B hp.1 hp.2 (fun i j => hA _ _)
      have hE : SmallBlockTriangular E :=
        ih (List.cons_ne_nil _ _) (fun d hd => hsizes d (List.mem_cons_of_mem _ hd))
          E (fun i j => hA _ _) htri.2
      have hid : A = upperBlock B C E := by
        ext i j
        obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
        obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
        change A (finSumFinEquiv i) (finSumFinEquiv j) =
          (fromBlocks B C 0 E) (finSumFinEquiv.symm (finSumFinEquiv i))
            (finSumFinEquiv.symm (finSumFinEquiv j))
        rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
        cases i <;> cases j
        · rfl
        · rfl
        · exact htri.1 _ _
        · rfl
      rw [hid]
      exact .upper C hB hE (fun i j => hA _ _)

/-- Conjecture 2 for an ordinary finite block upper triangular partition. -/
theorem conjecture_two_blocks_le_three (sizes : List ℕ) (hne : sizes ≠ [])
    (hsizes : ∀ p ∈ sizes, 1 ≤ p ∧ p ≤ 3)
    (A : SSP.MatrixMomentReduction.Mat sizes.sum)
    (hA : ∀ i j, 0 ≤ A i j) (htri : UpperTriangularBlocks sizes A)
    (u v : Fin sizes.sum → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log
      (SSP.MatrixMomentReduction.pairing A u v t/t^(sizes.sum-1))) :=
  conjecture_two_small_blocks A (smallBlockTriangular_of_partition sizes hne hsizes A hA htri)
    u v hu hv

/-- The all-k Conjecture 1 inequality for the same ordinary block partition. -/
theorem conjecture_one_blocks_le_three (sizes : List ℕ) (hne : sizes ≠ [])
    (hsizes : ∀ p ∈ sizes, 1 ≤ p ∧ p ≤ 3)
    (P : SSP.MatrixMomentReduction.Mat sizes.sum)
    (hP : ∀ i j, 0 ≤ P i j) (htri : UpperTriangularBlocks sizes P)
    (u v : Fin sizes.sum → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (rate atom : ℝ) (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ((sizes.sum+k : ℕ) : ℝ)/((sizes.sum+k-1 : ℕ) : ℝ)*rawMoment P u v rate atom k^2 ≤
      rawMoment P u v rate atom (k-1)*rawMoment P u v rate atom (k+1) :=
  conjecture_one_small_blocks P (smallBlockTriangular_of_partition sizes hne hsizes P hP htri)
    u v hu hv rate atom hrate hatom hρ k hk

/-- An arbitrary permutation of an ordinary block partition is allowed. -/
theorem smallBlockTriangular_of_reindexed_partition {s : ℕ}
    (A : SSP.MatrixMomentReduction.Mat s) (e : Fin s ≃ Fin s)
    (sizes : List ℕ) (hsum : sizes.sum = s) (hne : sizes ≠ [])
    (hsizes : ∀ p ∈ sizes, 1 ≤ p ∧ p ≤ 3)
    (hA : ∀ i j, 0 ≤ A i j)
    (htri : UpperTriangularBlocks sizes
      (Matrix.reindex (e.trans (finCongr hsum.symm))
        (e.trans (finCongr hsum.symm)) A)) : SmallBlockTriangular A := by
  subst s
  have h := smallBlockTriangular_of_partition sizes hne hsizes
    (Matrix.reindex e e A) (fun i j => hA _ _) (by simpa using htri)
  have hr := h.reindex e.symm
  have hid : Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by
    ext i j
    change A (e.symm (e i)) (e.symm (e j)) = A i j
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rwa [hid] at hr

/-- Transposition exchanges the actual exponential entries. -/
theorem expEntry_transpose {s : ℕ} (A : SSP.MatrixMomentReduction.Mat s)
    (i j : Fin s) (t : ℝ) : expEntry A.transpose i j t = expEntry A j i t := by
  apply HasSum.unique (expEntry_series _ _ _ t)
  convert expEntry_series A j i t using 1
  funext k
  rw [← Matrix.transpose_pow]
  rfl

theorem EntriesLogConvex.transpose {s p : ℕ}
    {A : SSP.MatrixMomentReduction.Mat s} (h : EntriesLogConvex A p) :
    EntriesLogConvex A.transpose p := by
  intro i j
  rw [show expEntry A.transpose i j = expEntry A j i from funext (expEntry_transpose A i j)]
  exact h j i

/-- Lower triangular decompositions satisfy Conjecture 2 as well. -/
theorem conjecture_two_small_lower_blocks {s : ℕ}
    (A : SSP.MatrixMomentReduction.Mat s) (hA : SmallBlockTriangular A.transpose)
    (u v : Fin s → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log
      (SSP.MatrixMomentReduction.pairing A u v t/t^(s-1))) := by
  have h : EntriesLogConvex A (s-1) := by
    simpa only [Matrix.transpose_transpose] using hA.entriesLogConvex.transpose
  exact (h.pairing u v hu hv).convex

/-- The corresponding Conjecture 1 inequality for lower triangular blocks. -/
theorem conjecture_one_small_lower_blocks {s : ℕ}
    (P : SSP.MatrixMomentReduction.Mat s) (hP : SmallBlockTriangular P.transpose)
    (u v : Fin s → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (rate atom : ℝ) (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ((s+k : ℕ) : ℝ)/((s+k-1 : ℕ) : ℝ)*rawMoment P u v rate atom k^2 ≤
      rawMoment P u v rate atom (k-1)*rawMoment P u v rate atom (k+1) := by
  exact conjecture_one_of_pairing_logConvex hP.dimension_pos P u v rate atom
    (fun i j => hP.nonneg j i) hu hv hrate hatom hρ
    (conjecture_two_small_lower_blocks _ (hP.smul hrate.le) u v hu hv) k hk

end SSP.BlockTriangular
