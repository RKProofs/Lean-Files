import SSPLean.QSequenceCrossing
import SSPLean.K2ShortProof
import SSPLean.QSequenceEquality
import SSPLean.SmallBlockTriangularPartition
import SSPLean.BStability
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sort

/-! Supporting proofs for the statement-by-statement audit of `main_revised.tex`.
These results do not import `MainRevised`, so that its paper-facing declarations
can use them without an import cycle. -/

set_option autoImplicit false
open Finset Matrix
open scoped Matrix.Norms.Operator

namespace SSP.MainRevisedSupport

/-- The actual matrix Neumann-square series, including convergence. -/
theorem neumann_square_hasSum {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hρ : spectralRadius ℂ (Q.map (algebraMap ℝ ℂ)) < 1) :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) • Q ^ k) ((1 - Q)⁻¹ * (1 - Q)⁻¹) := by
  obtain ⟨θ, hθ0, hθ1, C, hC0, hC⟩ :=
    SSP.exists_geometric_bound_of_spectralRadius_lt_one s Q hρ
  have hn : Summable (fun k : ℕ => ‖Q ^ k‖) :=
    ((summable_geometric_of_lt_one hθ0 hθ1).mul_left C).of_nonneg_of_le
      (fun _ => norm_nonneg _) hC
  have h := hasSum_sum_range_mul_of_summable_norm hn hn
  have hinv : (∑' k : ℕ, Q ^ k) = (1 - Q)⁻¹ := SSP.tsum_pow_eq_inv_one_sub Q hρ
  convert h using 1
  all_goals try rfl
  · funext n
    have he : ∑ j ∈ range (n + 1), Q ^ j * Q ^ (n - j) =
      ∑ _j ∈ range (n + 1), Q ^ n := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    rw [he]
    simp only [Finset.sum_const, Finset.card_range]
    ext i j
    simp
  · congr 1 <;> exact hinv.symm

/-- Lemma 4 in series form, obtained from the component bound and the
convergent matrix Neumann series (including its square). -/
theorem substochastic_sequence_inequality (s : ℕ) (hs : 0 < s)
    (Q : ℕ → ℕ → ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (hρ : spectralRadius ℂ ((SSP.toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (i : Fin s) :
    (∑' k : ℕ, ((SSP.toMat s Q) ^ k).mulVec (fun _ => (1 : ℝ)) i) ^ 2 ≤
      (2 * s / (s + 1)) *
        ∑' k : ℕ, ((k : ℝ) + 1) *
          ((SSP.toMat s Q) ^ k).mulVec (fun _ => (1 : ℝ)) i := by
  let R := SSP.Semigroup.rowFun (fun _ : Fin s => (1 : ℝ)) i
  have h1 := R.hasSum
    ((SSP.summable_pow_of_spectralRadius_lt_one (SSP.toMat s Q) hρ).hasSum)
  rw [SSP.tsum_pow_eq_inv_one_sub _ hρ] at h1
  have h2 := R.hasSum (neumann_square_hasSum (SSP.toMat s Q) hρ)
  have hcb := SSP.componentBound_unconditional s Q hQ hsub hρ hs i i.isLt
  have e1 : SSP.rowSum s (SSP.Nmat s Q) i =
      ((1 - SSP.toMat s Q)⁻¹).mulVec (fun _ => (1 : ℝ)) i := by
    rw [show SSP.rowSum s (SSP.Nmat s Q) i =
      SSP.rowSum s (SSP.invMat s Q) i from
        Finset.sum_congr rfl (fun j hj =>
          SSP.Nmat_eq_invMat s Q hρ i j i.isLt (mem_range.mp hj))]
    exact SSP.Bridge.rowSum_invMat_eq Q i i.isLt
  have e2 : SSP.rowSum2 s (SSP.Nmat s Q) i =
      ((1 - SSP.toMat s Q)⁻¹ * (1 - SSP.toMat s Q)⁻¹).mulVec
        (fun _ => (1 : ℝ)) i := by
    rw [show SSP.rowSum2 s (SSP.Nmat s Q) i =
      SSP.rowSum2 s (SSP.invMat s Q) i from
        Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun l hl => by
          rw [SSP.Nmat_eq_invMat s Q hρ i j i.isLt (mem_range.mp hj),
            SSP.Nmat_eq_invMat s Q hρ j l (mem_range.mp hj) (mem_range.mp hl)]))]
    rw [← Matrix.mulVec_mulVec]
    exact SSP.Bridge.rowSum2_invMat_eq Q i i.isLt
  rw [e1, e2] at hcb
  simpa [R, SSP.Semigroup.rowFun_apply, Matrix.smul_mulVec, Pi.smul_apply] using
    (show (∑' k : ℕ, R ((SSP.toMat s Q) ^ k)) ^ 2 ≤
      (2 * s / (s + 1)) * ∑' k : ℕ, R (((k : ℝ) + 1) • (SSP.toMat s Q) ^ k) by
        rw [h1.tsum_eq, h2.tsum_eq]
        exact hcb)

/-- The paper's algebraic lemma, including the `w=0` convention. -/
theorem algebraic_inequality (n : ℕ) (hn : 2 ≤ n) (w u β : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w < 1) (hu : 0 ≤ u)
    (hβ : (n : ℝ) / (n - 1) * w ^ 2 ≤ β) (hzero : w = 0 → β = 0) :
    (n + 2 : ℝ) / (n + 1) * (2 * (1 - w) + u + β) ^ 2 ≤
      3 * (1 - w) * (2 * (1 - w) + u + β) + 3 * u +
        (n + 1 : ℝ) / n * (u ^ 2 / (1 - w) + β ^ 2 / w) := by
  by_cases hw : w = 0
  · subst w
    rw [hzero rfl]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hid :
        (n + 1 : ℝ) * (3 * (2 + u) + 3 * u + (n + 1 : ℝ) / n * u ^ 2)
          - (n + 2 : ℝ) * (2 + u) ^ 2 =
        u ^ 2 / n + (2 * n - 2) * u + 2 * n - 2 := by
      field_simp
      ring
    simp only [sub_zero, mul_one, zero_pow (by omega : 2 ≠ 0), zero_div, add_zero,
      div_one]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)]
    have hp : 0 ≤ u ^ 2 / n + (2 * n - 2) * u + 2 * n - 2 := by
      have : 0 ≤ (2 : ℝ) * n - 2 := by linarith
      nlinarith [div_nonneg (sq_nonneg u) hn0.le,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * n - 2) hu]
    nlinarith only [hid, hp]
  · have h := SSP.K2Short.quadratic_nonneg n hn w u β (lt_of_le_of_ne hw0 (Ne.symm hw))
      hw1 hu hβ
    unfold SSP.K2Short.G at h
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)]
    nlinarith only [h]

/-- A triangular matrix is a composition of one-state blocks.  The induction
uses only the one-state exponential and block convolution, not any cyclic
two- or three-state conjecture. -/
theorem triangular_entriesLogConvex {s : ℕ} (hs : 1 ≤ s)
    (A : SSP.MatrixMomentReduction.Mat s) (hA : ∀ i j, 0 ≤ A i j)
    (htri : ∀ i j, j < i → A i j = 0) :
    SSP.BlockTriangular.EntriesLogConvex A (s - 1) := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hs1 : s = 1
    · subst s
      exact SSP.BlockTriangular.entriesLogConvex_one A hA
    · obtain ⟨q, rfl⟩ : ∃ q, s = 1 + q := ⟨s - 1, by omega⟩
      have hq : 1 ≤ q := by omega
      let B := A.submatrix (Fin.castAdd q) (Fin.castAdd q)
      let C := A.submatrix (Fin.castAdd q) (Fin.natAdd 1)
      let E := A.submatrix (Fin.natAdd 1) (Fin.natAdd 1)
      have hB := SSP.BlockTriangular.entriesLogConvex_one B (fun i j => hA _ _)
      have hE : SSP.BlockTriangular.EntriesLogConvex E (q - 1) := by
        apply ih q (by omega) hq E (fun i j => hA _ _)
        intro i j hij
        exact htri _ _ (by simpa using hij)
      have hid : A = SSP.BlockTriangular.upperBlock B C E := by
        ext i j
        obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
        obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
        change A (finSumFinEquiv i) (finSumFinEquiv j) =
          (fromBlocks B C 0 E) (finSumFinEquiv.symm (finSumFinEquiv i))
            (finSumFinEquiv.symm (finSumFinEquiv j))
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        cases i <;> cases j
        · rfl
        · rfl
        · exact htri _ _ (by simp [Fin.lt_def])
        · rfl
      rw [hid]
      exact (SSP.BlockTriangular.entriesLogConvex_fromBlocks (by omega) hq
        B C E hB hE (fun i j => hA _ _)).reindex finSumFinEquiv

/-- The all-k acyclic hierarchy from the actual triangular matrix. -/
theorem acyclic_hierarchy {s : ℕ} (hs : 1 ≤ s)
    (P : SSP.MatrixMomentReduction.Mat s) (hP : ∀ i j, 0 ≤ P i j)
    (htri : ∀ i j, j < i → P i j = 0)
    (u v : Fin s → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (rate atom : ℝ) (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ((s + k : ℕ) : ℝ) / ((s + k - 1 : ℕ) : ℝ) *
        SSP.MatrixMomentReduction.rawMoment P u v rate atom k ^ 2 ≤
      SSP.MatrixMomentReduction.rawMoment P u v rate atom (k - 1) *
        SSP.MatrixMomentReduction.rawMoment P u v rate atom (k + 1) := by
  apply SSP.MatrixMomentReduction.conjecture_one_of_pairing_logConvex hs P u v rate atom
    hP hu hv hrate hatom hρ _ k hk
  exact ((triangular_entriesLogConvex hs (rate • P)
    (fun i j => mul_nonneg hrate.le (hP i j))
    (fun i j hij => by simp [htri i j hij])).pairing u v hu hv).convex

/-- Positive mean implies positivity of every positive-index raw density moment. -/
theorem rawMoment_pos_of_mean_pos {d : ℕ}
    (P : SSP.MatrixMomentReduction.Mat d) (hP : ∀ i j, 0 ≤ P i j)
    (u v : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (rate atom : ℝ) (hrate : 0 < rate)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1)
    (hm : 0 < SSP.MatrixMomentReduction.rawMoment P u v rate atom 1)
    (k : ℕ) (hk : 1 ≤ k) :
    0 < SSP.MatrixMomentReduction.rawMoment P u v rate atom k := by
  open SSP.MatrixMomentReduction in
  have hzero : pairing (rate • P) u v ≠ 0 := by
    intro hz
    have hd : density P u v rate = 0 := by
      rw [density_uniformization, hz]
      ext t
      simp
    simp [rawMoment, hd, SSP.MomentReduction.moment] at hm
  have hpF := SSP.MatrixMomentReduction.pairing_pos (rate • P) u v
    (fun i j => mul_nonneg hrate.le (hP i j)) hu hv hzero
  have hp : ∀ t, 0 < t → 0 < SSP.MatrixMomentReduction.density P u v rate t := by
    intro t ht
    rw [SSP.MatrixMomentReduction.density_uniformization]
    exact mul_pos (Real.exp_pos _) (hpF t ht)
  obtain ⟨c, hc, hdec, _⟩ :=
    SSP.MatrixMomentReduction.density_decay P u v rate hrate hρ
  have h := SSP.MomentReduction.moment_pos _ k hp
    (SSP.MomentReduction.weighted_integrable _
      (SSP.MatrixMomentReduction.density_continuous P u v rate).continuousOn c hc hdec k)
  simpa [SSP.MatrixMomentReduction.rawMoment, show k ≠ 0 by omega] using h

/-- The paper's positive-moment ratio form, with at most `s` acyclic states. -/
theorem acyclic_hierarchy_ratio {d s : ℕ} (hd : 1 ≤ d) (hds : d ≤ s)
    (P : SSP.MatrixMomentReduction.Mat d) (hP : ∀ i j, 0 ≤ P i j)
    (htri : ∀ i j, j < i → P i j = 0)
    (u v : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (rate atom : ℝ) (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1)
    (hm : 0 < SSP.MatrixMomentReduction.rawMoment P u v rate atom 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ((s + k : ℕ) : ℝ) / ((s + k - 1 : ℕ) : ℝ) ≤
      SSP.MatrixMomentReduction.rawMoment P u v rate atom (k - 1) *
        SSP.MatrixMomentReduction.rawMoment P u v rate atom (k + 1) /
          SSP.MatrixMomentReduction.rawMoment P u v rate atom k ^ 2 := by
  have hpos := rawMoment_pos_of_mean_pos P hP u v hu hv rate atom hrate hρ hm k hk
  have hcoef : ((s + k : ℕ) : ℝ) / ((s + k - 1 : ℕ) : ℝ) ≤
      ((d + k : ℕ) : ℝ) / ((d + k - 1 : ℕ) : ℝ) := by
    have hsden : (0 : ℝ) < ((s + k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < s+k-1)
    have hdden : (0 : ℝ) < ((d + k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d+k-1)
    rw [div_le_div_iff₀ hsden hdden]
    have hes : ((s + k : ℕ) : ℝ) = ((s + k - 1 : ℕ) : ℝ) + 1 := by norm_cast; omega
    have hed : ((d + k : ℕ) : ℝ) = ((d + k - 1 : ℕ) : ℝ) + 1 := by norm_cast; omega
    have hle : ((d + k - 1 : ℕ) : ℝ) ≤ ((s + k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : d+k-1 ≤ s+k-1)
    rw [hes, hed]
    nlinarith
  apply hcoef.trans
  rw [le_div_iff₀ (sq_pos_of_pos hpos)]
  exact acyclic_hierarchy hd P hP htri u v hu hv rate atom hrate hatom hρ k hk

/-- Every finite real vector can be sorted by a permutation, with ties allowed. -/
theorem exists_sorted_permutation {s : ℕ} (c : Fin s → ℝ) :
    ∃ e : Fin s ≃ Fin s, Monotone (c ∘ e) := by
  classical
  let R : Fin s → Fin s → Prop := fun i j => c i ≤ c j
  letI : IsTrans (Fin s) R := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Total R := ⟨fun _ _ => le_total _ _⟩
  letI : Std.Refl R := ⟨fun _ => le_rfl⟩
  let l := ((Finset.univ : Finset (Fin s)).toList).mergeSort (fun i j => decide (R i j))
  have hperm : l.Perm (Finset.univ : Finset (Fin s)).toList := List.mergeSort_perm _ _
  have hlen : l.length = s := by rw [hperm.length_eq]; simp
  let e := (finCongr hlen.symm).trans
    (List.Nodup.getEquivOfForallMemList l (hperm.nodup_iff.mpr (Finset.nodup_toList _))
      (fun i => hperm.mem_iff.mpr (by simp)))
  refine ⟨e, ?_⟩
  intro i j hij
  have hsort : l.Pairwise R := List.pairwise_mergeSort' R _
  exact hsort.rel_get_of_le (by simpa using hij)

/-- Finite sums are invariant under a simultaneous relabeling of two indices. -/
theorem sum_reindex_two {s : ℕ} (e : Fin s ≃ Fin s) (f : Fin s → Fin s → ℝ) :
    (∑ i, ∑ j, f (e i) (e j)) = ∑ i, ∑ j, f i j := by
  simp_rw [e.sum_comp]
  exact e.sum_comp (fun i => ∑ j, f i j)

/-- The algebraic-stability barrier without a sorted-stage hypothesis. -/
theorem barrier_unsorted {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) (b c : Fin s → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hb : ∀ i, 0 ≤ b i)
    (hrow : ∀ i, ∑ j, A i j = c i)
    (h1 : ∑ i, b i = 1) (h2 : ∑ i, b i * c i = 1 / 2)
    (h3 : ∑ i, b i * c i ^ 2 = 1 / 3)
    (hM : ∀ x : Fin s → ℝ, 0 ≤ ∑ i, ∑ j,
      (b i * A i j + b j * A j i - b i * b j) * (x i * x j)) : False := by
  classical
  obtain ⟨e, he⟩ := exists_sorted_permutation c
  let bp : ℕ → ℝ := fun i => if hi : i < s then b (e ⟨i, hi⟩) else 0
  let cp : ℕ → ℝ := fun i => if hi : i < s then c (e ⟨i, hi⟩) else 0
  let Ap : ℕ → ℕ → ℝ := fun i j =>
    if hi : i < s then if hj : j < s then A (e ⟨i, hi⟩) (e ⟨j, hj⟩) else 0 else 0
  have eb (i : Fin s) : bp i = b (e i) := by simp [bp, i.isLt]
  have ec (i : Fin s) : cp i = c (e i) := by simp [cp, i.isLt]
  have eA (i j : Fin s) : Ap i j = A (e i) (e j) := by simp [Ap, i.isLt, j.isLt]
  apply SSP.no_order3_algebraically_stable (A := Ap) (b := bp) (c := cp)
  · intro i j
    dsimp [Ap]
    split <;> try positivity
    split <;> try positivity
    exact hA _ _
  · intro i
    dsimp [bp]
    split
    · exact hb _
    · exact le_rfl
  · intro i j hij hj
    have hi : i < s := lt_of_le_of_lt hij hj
    simpa [cp, hi, hj, Function.comp_def] using
      he (show (⟨i, hi⟩ : Fin s) ≤ ⟨j, hj⟩ from hij)
  · intro i hi
    rw [← Fin.sum_univ_eq_sum_range (fun j => Ap i j) s]
    have hsum : (∑ j : Fin s, Ap i j) = ∑ j : Fin s, A (e ⟨i, hi⟩) (e j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact eA ⟨i, hi⟩ j
    rw [hsum, e.sum_comp, hrow]
    simp [cp, hi]
  · rw [← Fin.sum_univ_eq_sum_range bp s]
    simp_rw [eb]
    exact (e.sum_comp b).trans h1
  · rw [← Fin.sum_univ_eq_sum_range (fun i => bp i * cp i) s]
    simp_rw [eb, ec]
    exact (e.sum_comp (fun i => b i * c i)).trans h2
  · rw [← Fin.sum_univ_eq_sum_range (fun i => bp i * cp i ^ 2) s]
    simp_rw [eb, ec]
    exact (e.sum_comp (fun i => b i * c i ^ 2)).trans h3
  · intro x
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range s,
      (bp i * Ap i j + bp j * Ap j i - bp i * bp j) * (x i * x j)) s]
    simp_rw [← Fin.sum_univ_eq_sum_range (fun j =>
      (bp _ * Ap _ j + bp j * Ap j _ - bp _ * bp j) * (x _ * x j)) s]
    simp_rw [eb, eA]
    have h := hM (fun i => x (e.symm i))
    rw [← sum_reindex_two e (fun i j =>
      (b i * A i j + b j * A j i - b i * b j) * (x (e.symm i) * x (e.symm j)))] at h
    simpa only [Equiv.symm_apply_apply] using h

end SSP.MainRevisedSupport
