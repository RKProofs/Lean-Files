import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic

/-!
# `ρ(Q) < 1` for a substochastic nonnegative matrix with `I − Q` invertible

For a nonnegative real matrix `Q` with row sums `≤ 1` (`Qe ≤ e`) and `I − Q` invertible, the
spectral radius satisfies `ρ(Q) < 1`.

The elementary half `ρ(Q) ≤ 1` (from the `L∞` operator norm = max row sum `≤ 1`) is proved in
`spectralRadius_le_one`.  The full bound `ρ(Q) < 1` is then established **without
Perron–Frobenius** in `Elementary.spectralRadius_lt_one_elementary`: the argument rules out a
modulus-`1` eigenvalue directly (an argmax-modulus index set is forward-closed and its diagonal
block has the constant vector as an eigenvalue `1`, contradicting `I − Q` invertible), so no
Perron–Frobenius input — and no `weak_perron_frobenius` hypothesis — is needed.
-/

open Finset Matrix
open scoped Matrix.Norms.Operator ENNReal NNReal

namespace SSP

/-- **`ρ(Q) ≤ 1` from substochasticity.**  If `Q ≥ 0` and every row sum is `≤ 1`, then the
L∞ operator norm is `≤ 1`, so `spectralRadius ℝ Q ≤ 1`. -/
lemma spectralRadius_le_one {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) :
    spectralRadius ℝ Q ≤ 1 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · -- `Fin 0`: the matrix ring is trivial, spectrum is empty, spectralRadius = 0.
    simp only [spectralRadius]
    apply iSup₂_le
    intro k hk
    exfalso
    rw [spectrum.mem_iff] at hk
    apply hk
    rw [Subsingleton.elim (algebraMap ℝ (Matrix (Fin 0) (Fin 0) ℝ) k - Q) 1]
    exact isUnit_one
  · haveI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
    -- `spectralRadius ℝ Q ≤ ‖Q‖₊`
    refine (spectrum.spectralRadius_le_nnnorm Q).trans ?_
    -- reduce to `‖Q‖₊ ≤ 1`, i.e. `‖Q‖ ≤ 1`
    rw [← ENNReal.coe_one, ENNReal.coe_le_coe, Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    have hsum : (∑ j, ‖Q i j‖₊ : ℝ≥0) = ⟨∑ j, Q i j, Finset.sum_nonneg fun j _ => hQ i j⟩ := by
      ext
      push_cast
      exact Finset.sum_congr rfl fun j _ => by
        simp [Real.norm_eq_abs, abs_of_nonneg (hQ i j)]
    rw [hsum]
    exact_mod_cast hrow i

/-!
## The proof of `ρ(Q) < 1`

Everything below is self-contained: it derives `ρ(Q) < 1` from the elementary argument in
`spectral_radius_substochastic.tex`, with **no** appeal to Perron–Frobenius.  The argument: any
eigenvalue has modulus `≤ 1`; if some complex eigenvalue had modulus exactly `1`, its
argmax-modulus index set `S` would be forward-closed with every row summing to `1`, making the
constant-`1` vector an eigenvector of the `S`-diagonal block at eigenvalue `1`, so
`1 ∈ spectrum Q`, contradicting `I − Q` invertible.  (Supporting spectral lemmas keep their `'`
suffix from an earlier revision.)
-/

namespace Elementary

/-- Spectrum finiteness ⇒ the complex spectral radius is not `⊤`.  (Local, PF-free copy.) -/
theorem specRadius_ne_top' {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) :
    spectralRadius ℂ (Q.map (algebraMap ℝ ℂ)) ≠ ⊤ := by
  have : Finite (spectrum ℂ (Q.map (algebraMap ℝ ℂ))) := Matrix.instFiniteSpectrum _
  rw [spectralRadius, iSup_subtype']
  exact iSup_ne_top (fun z => ENNReal.coe_ne_top)

/-- The complex spectrum of the complexification of a (nonempty-index) matrix is nonempty.
(Local, PF-free copy.) -/
theorem specC_nonempty' {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (Q : Matrix n n ℝ) :
    (spectrum ℂ (Q.map (algebraMap ℝ ℂ))).Nonempty := by
  have hdeg : (Q.map (algebraMap ℝ ℂ)).charpoly.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (Q.map (algebraMap ℝ ℂ)).charpoly_monic.ne_zero,
      Matrix.charpoly_natDegree_eq_dim]
    exact_mod_cast (Fintype.card_pos).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨z, Matrix.mem_spectrum_iff_isRoot_charpoly.2 hz⟩

/-- The complex spectral radius (as a real) is achieved by the modulus of some complex eigenvalue.
(Local, PF-free copy.) -/
theorem exists_specC_norm_eq_specRadius' {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (Q : Matrix n n ℝ) :
    ∃ z ∈ spectrum ℂ (Q.map (algebraMap ℝ ℂ)),
      ‖z‖ = (spectralRadius ℂ (Q.map (algebraMap ℝ ℂ))).toReal := by
  obtain ⟨z, hz, hznorm⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty (specC_nonempty' Q)
  refine ⟨z, hz, ?_⟩
  rw [← hznorm]
  simp [Complex.norm_def, coe_nnnorm]

open Polynomial in
/-- Forward-closed charpoly factorization.  (Local, PF-free copy of
`charpoly_split_of_forwardClosed`.) -/
theorem charpoly_split_fc {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] (M : Matrix n n R) (p : n → Prop) [DecidablePred p]
    (h : ∀ i, p i → ∀ j, ¬ p j → M i j = 0) :
    M.charpoly =
      (M.toSquareBlockProp p).charpoly * (M.toSquareBlockProp (fun i => ¬ p i)).charpoly := by
  have hreindex :
      (Matrix.reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm M) =
        Matrix.fromBlocks (M.toSquareBlockProp p) 0
          (M.toBlock (fun i => ¬ p i) p) (M.toSquareBlockProp (fun i => ¬ p i)) := by
    ext i j
    rcases i with a | a <;> rcases j with b | b <;>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.toSquareBlockProp_def, Matrix.toBlock_apply, Matrix.of_apply, Matrix.zero_apply]
    · exact h a a.2 b b.2
  calc M.charpoly
      = (Matrix.reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm M).charpoly :=
        (Matrix.charpoly_reindex _ _).symm
    _ = _ := by rw [hreindex, Matrix.charpoly_fromBlocks_zero₁₂]

open Polynomial in
/-- A real number in the spectrum of a forward-closed diagonal block lies in the spectrum of the
whole matrix.  (Local, PF-free copy of `specR_block_subset`.) -/
theorem block_specR_subset {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) (p : n → Prop) [DecidablePred p]
    (h : ∀ i, p i → ∀ j, ¬ p j → Q i j = 0) {r : ℝ}
    (hr : r ∈ spectrum ℝ (Q.toSquareBlockProp p)) : r ∈ spectrum ℝ Q := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hr ⊢
  rw [charpoly_split_fc Q p h]
  exact Polynomial.root_mul_right_of_isRoot _ hr

/-- **No complex eigenvalue of modulus `1`.**  For a nonnegative substochastic `Q` (row sums
`≤ 1`) with `I − Q` invertible, no eigenvalue of the complexification has modulus exactly `1`.
This is the heart of the Perron–Frobenius-free argument. -/
theorem no_modulus_one {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hinv : IsUnit (1 - Q))
    {z : ℂ} (hz : z ∈ spectrum ℂ (Q.map (algebraMap ℝ ℂ))) :
    ‖z‖ ≠ 1 := by
  classical
  intro hznorm
  -- Extract a nonzero complex eigenvector `w` at `z`.
  rw [← Matrix.spectrum_toLin'] at hz
  obtain ⟨w, hw⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz).exists_hasEigenvector
  have hwne : w ≠ 0 := hw.2
  have hweig : (Q.map (algebraMap ℝ ℂ)) *ᵥ w = z • w := by
    have := hw.apply_eq_smul
    rwa [Matrix.toLin'_apply] at this
  -- Entrywise eigenvalue equation: `∑ j, (Q i j) * w j = z * w i`.
  have hentry : ∀ i, ∑ j, (algebraMap ℝ ℂ (Q i j)) * w j = z * w i := by
    intro i
    have := congrFun hweig i
    simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
      using this
  -- Pointwise triangle-inequality bound `‖w i‖ = ‖z‖·‖w i‖ ≤ ∑ j, Q i j · ‖w j‖`.
  have hpoint : ∀ i, ‖w i‖ ≤ ∑ j, Q i j * ‖w j‖ := by
    intro i
    calc ‖w i‖ = ‖z‖ * ‖w i‖ := by rw [hznorm, one_mul]
      _ = ‖∑ j, (algebraMap ℝ ℂ (Q i j)) * w j‖ := by rw [hentry i, norm_mul]
      _ ≤ ∑ j, ‖(algebraMap ℝ ℂ (Q i j)) * w j‖ := norm_sum_le _ _
      _ = ∑ j, Q i j * ‖w j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Complex.coe_algebraMap, Complex.norm_of_nonneg (hQ i j)]
  -- The maximum modulus `R` and the argmax index set `S`.
  haveI : Nonempty (Fin s) := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · exact absurd (Subsingleton.elim w 0) hwne
    · exact ⟨⟨0, hs⟩⟩
  set R : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun k => ‖w k‖) with hR
  have hRge : ∀ j, ‖w j‖ ≤ R := fun j => Finset.le_sup' (fun k => ‖w k‖) (Finset.mem_univ j)
  set S : Fin s → Prop := fun i => ‖w i‖ = R with hSdef
  -- `R > 0` since `w ≠ 0`.
  have hRpos : 0 < R := by
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hwne
    exact lt_of_lt_of_le (norm_pos_iff.mpr hi₀) (hRge i₀)
  -- `S` is nonempty: the sup' is attained.
  obtain ⟨iS, _, hiS⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun k => ‖w k‖)
  have hSne : S iS := hiS.symm
  -- For `i ∈ S`: row `i` saturates (sum = 1) and is forward-closed (positive entries stay in `S`).
  have hkey : ∀ i, S i → (∑ j, Q i j = 1) ∧ (∀ j, ¬ S j → Q i j = 0) := by
    intro i hiS
    -- The chain `R = ‖w i‖ ≤ ∑ Q i j ‖w j‖ ≤ ∑ Q i j · R ≤ R` collapses to equalities.
    have hlo : R ≤ ∑ j, Q i j * ‖w j‖ := hiS ▸ hpoint i
    have hmid : ∑ j, Q i j * ‖w j‖ ≤ ∑ j, Q i j * R :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hRge j) (hQ i j)
    have hhi : ∑ j, Q i j * R ≤ R := by
      rw [← Finset.sum_mul]
      calc (∑ j, Q i j) * R ≤ 1 * R := mul_le_mul_of_nonneg_right (hrow i) hRpos.le
        _ = R := one_mul R
    -- From `R ≤ A ≤ B ≤ R` all three are equal to `R`.
    have hAeqR : ∑ j, Q i j * ‖w j‖ = R := le_antisymm (le_trans hmid hhi) hlo
    have hBeqR : ∑ j, Q i j * R = R := le_antisymm hhi (le_trans hlo hmid)
    -- Row saturation: `(∑ Q i j) · R = R`, and `R > 0`, so `∑ Q i j = 1`.
    have hsat : ∑ j, Q i j = 1 := by
      have hprod : (∑ j, Q i j) * R = 1 * R := by
        rw [Finset.sum_mul, hBeqR, one_mul]
      exact mul_right_cancel₀ hRpos.ne' hprod
    refine ⟨hsat, ?_⟩
    -- Forward-closed: `∑ Q i j · (R − ‖w j‖) = 0` with nonneg terms ⇒ each term `0`.
    have hzero : ∑ j, Q i j * (R - ‖w j‖) = 0 := by
      have hexp : ∑ j, Q i j * (R - ‖w j‖) = (∑ j, Q i j * R) - ∑ j, Q i j * ‖w j‖ := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hexp, hBeqR, hAeqR, sub_self]
    have hterm : ∀ j ∈ Finset.univ, Q i j * (R - ‖w j‖) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        mul_nonneg (hQ i j) (sub_nonneg.mpr (hRge j))).mp hzero
    intro j hjS
    rcases mul_eq_zero.mp (hterm j (Finset.mem_univ j)) with h | h
    · exact h
    · exact absurd (by rw [hSdef]; linarith [sub_eq_zero.mp h] : S j) hjS
  -- Now `S` is forward-closed, so `1 ∈ spectrum ℝ (Q.toSquareBlockProp S)` via the
  -- constant-`1` eigenvector, hence `1 ∈ spectrum ℝ Q`, contradicting `hinv`.
  have hfc : ∀ i, S i → ∀ j, ¬ S j → Q i j = 0 := fun i hi j hj => (hkey i hi).2 j hj
  have hone_block : (1 : ℝ) ∈ spectrum ℝ (Q.toSquareBlockProp S) := by
    -- The block index type is nonempty.
    haveI : Nonempty {a // S a} := ⟨⟨iS, hSne⟩⟩
    set A := Q.toSquareBlockProp S with hAdef
    by_contra hnot
    -- `1 ∉ spectrum` means `1 - A` is a unit.
    rw [spectrum.mem_iff, not_not] at hnot
    have hunit : IsUnit (1 - A) := by simpa using hnot
    have hdet : (1 - A).det ≠ 0 :=
      (Matrix.isUnit_iff_isUnit_det _ |>.mp hunit).ne_zero
    -- `(1 - A) *ᵥ 𝟙 = 0` from row saturation, but `𝟙 ≠ 0`.
    have hAmul : A *ᵥ (fun _ => (1 : ℝ)) = (fun _ => (1 : ℝ)) := by
      funext i
      have hi : S i.1 := i.2
      -- `(A *ᵥ 𝟙) i = ∑_{j : block} Q i.1 j.1 = ∑_{j : Fin s} Q i.1 j = 1`.
      have hblock : ∑ j : {a // S a}, A i j = ∑ j : Fin s, Q i.1 j := by
        have hAentry : ∀ j : {a // S a}, A i j = Q i.1 j.1 := fun j => rfl
        simp only [hAentry]
        -- `∑ j : {a//S a}, Q i.1 j.1 = ∑ j ∈ univ.filter S, Q i.1 j` (Finset.sum_subtype),
        -- and the dropped `¬S` terms vanish by forward-closedness.
        rw [← Finset.sum_subtype (Finset.univ.filter S)
              (fun x => by simp [Finset.mem_filter]) (fun j => Q i.1 j)]
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hjfilt
        have hjnS : ¬ S j := by
          simpa [Finset.mem_filter] using hjfilt
        exact (hkey i.1 hi).2 j hjnS
      simp only [Matrix.mulVec, dotProduct, mul_one]
      rw [hblock, (hkey i.1 hi).1]
    have hzerovec : (1 - A) *ᵥ (fun _ => (1 : ℝ)) = 0 := by
      rw [Matrix.sub_mulVec, hAmul, Matrix.one_mulVec, sub_self]
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet hzerovec
    exact one_ne_zero (congrFun this ⟨iS, hSne⟩)
  have h1notspec : (1 : ℝ) ∉ spectrum ℝ Q := by
    rw [spectrum.mem_iff, not_not]; simpa using hinv
  exact h1notspec (block_specR_subset Q S hfc hone_block)

/-- **`ρ(Q) < 1`, without Perron–Frobenius.**  For a nonnegative substochastic `Q` (row sums
`≤ 1`) with `I − Q` invertible, the complex spectral radius of the complexification is `< 1`.
This is a self-contained proof (see the section docstring): it does not use `weak_perron_frobenius`
or any lemma from the Perron–Frobenius modules. -/
theorem spectralRadius_lt_one_elementary {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hinv : IsUnit (1 - Q)) :
    spectralRadius ℂ (Q.map (algebraMap ℝ ℂ)) < 1 := by
  set ρc := spectralRadius ℂ (Q.map (algebraMap ℝ ℂ)) with hρc
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · -- `Fin 0`: the matrix ring is trivial, spectrum is empty, spectralRadius = 0.
    have hzero : ρc = 0 := by
      rw [hρc]
      simp only [spectralRadius]
      refine le_antisymm ?_ bot_le
      apply iSup₂_le
      intro k hk
      exfalso
      rw [spectrum.mem_iff] at hk
      apply hk
      rw [Subsingleton.elim (algebraMap ℂ (Matrix (Fin 0) (Fin 0) ℂ) k -
        Q.map (algebraMap ℝ ℂ)) 1]
      exact isUnit_one
    rw [hzero]
    exact zero_lt_one
  · haveI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
    -- Step 1: ρc ≤ 1 (max row sum of the L∞ operator norm).
    have hle : ρc ≤ 1 := by
      rw [hρc]
      refine (spectrum.spectralRadius_le_nnnorm _).trans ?_
      rw [← ENNReal.coe_one, ENNReal.coe_le_coe, Matrix.linfty_opNNNorm_def]
      refine Finset.sup_le fun i _ => ?_
      have hsum : (∑ j, ‖(Q.map (algebraMap ℝ ℂ)) i j‖₊ : ℝ≥0) =
          ⟨∑ j, Q i j, Finset.sum_nonneg fun j _ => hQ i j⟩ := by
        ext
        push_cast
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.map_apply, Complex.coe_algebraMap, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (hQ i j)]
      rw [hsum]
      exact_mod_cast hrow i
    -- Step 2: ρc ≠ ⊤.
    have hρc_top : ρc ≠ ⊤ := specRadius_ne_top' Q
    -- Step 3: the spectral radius is achieved by some eigenvalue `z₀`, and `‖z₀‖ < 1`.
    obtain ⟨z₀, hz₀mem, hz₀eq⟩ := exists_specC_norm_eq_specRadius' Q
    rw [← hρc] at hz₀eq
    have hz₀le : ‖z₀‖ ≤ 1 := by
      rw [hz₀eq, ← ENNReal.toReal_one]
      exact ENNReal.toReal_mono (by simp) hle
    have hz₀ne : ‖z₀‖ ≠ 1 := no_modulus_one Q hQ hrow hinv hz₀mem
    have hlt_real : ρc.toReal < 1 := by
      rw [← hz₀eq]; exact lt_of_le_of_ne hz₀le hz₀ne
    -- Step 4: ρc < 1.
    rw [← ENNReal.toReal_one] at hlt_real
    exact (ENNReal.toReal_lt_toReal hρc_top (by simp)).mp hlt_real

end Elementary

end SSP
