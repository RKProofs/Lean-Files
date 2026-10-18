import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic
import SSPLean.QSequencePaths
import SSPLean.QSequencePaths

/-!
# Geometric decay of matrix powers from `ρ(Q) < 1`

This module supplies the convergence input for the Neumann series `N = Σ Qᵏ` under the
paper's actual hypothesis `ρ(Q) < 1` (spectral radius), rather than the stronger uniform
strict-substochasticity used internally by `QSequencePaths.lean`.

The main export is `rowSum_decay_of_spectralRadius`: for a nonnegative `Q : ℕ → ℕ → ℝ` whose
`Fin s` view has complex spectral radius `< 1`, there are `θ < 1` and `C` with
`(Qᵏ e)ᵢ ≤ C · θᵏ` for all `k` and `i < s`.  This is exactly the `RowSumDecay` predicate that
`QSequencePaths.lean` consumes, so it lets the whole development run under `ρ(Q) < 1`.

The route is: Gelfand's formula over `ℂ` (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_
spectralRadius`) gives `‖Qᵏ‖ ≤ C·θᵏ` in the L∞ operator norm (via the complexification
isometry `linfty_opNorm_map_algebraMap`); a nonnegative matrix's row sum `(Qᵏe)ᵢ` is bounded
by that operator norm; and `matPow_eq_toMat_pow` bridges the file's `matPow` to the genuine
matrix power.
-/

open Finset Matrix
open scoped Matrix.Norms.Operator ENNReal NNReal

namespace SSP

/-- The complexification map `Matrix.map (algebraMap ℝ ℂ)` is an isometry for the
L∞ operator norm. -/
lemma linfty_opNorm_map_algebraMap {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) :
    ‖A.map (algebraMap ℝ ℂ)‖ = ‖A‖ := by
  rw [linfty_opNorm_def, linfty_opNorm_def]
  congr 1
  apply Finset.sup_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.map_apply, Complex.coe_algebraMap, Complex.nnnorm_real]

/-- **Geometric decay of matrix powers from `ρ(Q) < 1`.**  If the (complex) spectral radius
of `Q` is `< 1`, then there is a rate `θ < 1` and a constant `C` with `‖Qᵏ‖ ≤ C · θᵏ` in the
L∞ operator norm. -/
lemma exists_geometric_bound_of_spectralRadius_lt_one
    (s : ℕ) (Q : Matrix (Fin s) (Fin s) ℝ)
    (hρ : spectralRadius ℂ (Q.map (algebraMap ℝ ℂ)) < 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ‖Q ^ k‖ ≤ C * θ ^ k := by
  set Qc : Matrix (Fin s) (Fin s) ℂ := Q.map (algebraMap ℝ ℂ) with hQc
  have hnorm : ∀ k, ‖Q ^ k‖ = ‖Qc ^ k‖ := by
    intro k
    rw [hQc, ← Matrix.map_pow, linfty_opNorm_map_algebraMap]
  have hρlt : spectralRadius ℂ Qc < 1 := hρ
  obtain ⟨θ, hθpos, hθρ, hθ1⟩ :
      ∃ θ : ℝ, 0 < θ ∧ spectralRadius ℂ Qc < ENNReal.ofReal θ ∧ θ < 1 := by
    have hρne : spectralRadius ℂ Qc ≠ ⊤ := hρlt.ne_top
    set r := (spectralRadius ℂ Qc).toReal with hr
    have hr1 : r < 1 := by
      rw [hr, ← ENNReal.toReal_one]
      exact (ENNReal.toReal_lt_toReal hρne (by simp)).mpr hρlt
    have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
    refine ⟨(r + 1) / 2, by linarith, ?_, by linarith⟩
    have hmid : r < (r + 1) / 2 := by linarith
    calc spectralRadius ℂ Qc = ENNReal.ofReal r := by
            rw [hr, ENNReal.ofReal_toReal hρne]
      _ < ENNReal.ofReal ((r + 1) / 2) := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hmid
  have hθ0 : 0 ≤ θ := hθpos.le
  refine ⟨θ, hθ0, hθ1, ?_⟩
  have hgelfand := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius Qc
  have hev := hgelfand.eventually_lt_const hθρ
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have htail : ∀ n, N ≤ n → 1 ≤ n → ‖Qc ^ n‖ ≤ θ ^ n := by
    intro n hnN hn1
    have hlt := hN n hnN
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hpow : ((‖Qc ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) ^ (n : ℝ)
        < (ENNReal.ofReal θ) ^ (n : ℝ) :=
      ENNReal.rpow_lt_rpow hlt hnpos
    rw [← ENNReal.rpow_mul] at hpow
    rw [one_div, inv_mul_cancel₀ (by positivity), ENNReal.rpow_one] at hpow
    have hrhs : (ENNReal.ofReal θ) ^ (n : ℝ) = ENNReal.ofReal (θ ^ n) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hθ0 (by positivity), Real.rpow_natCast]
    rw [hrhs] at hpow
    have hle := hpow.le
    rw [← ENNReal.toReal_le_toReal (by simp) ENNReal.ofReal_ne_top,
        ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity)] at hle
    rwa [coe_nnnorm] at hle
  set M := max N 1 with hM
  set C := 1 + ∑ n ∈ Finset.range M, ‖Qc ^ n‖ / θ ^ n with hC
  have hsum0 : 0 ≤ ∑ n ∈ Finset.range M, ‖Qc ^ n‖ / θ ^ n :=
    Finset.sum_nonneg (fun n _ => by positivity)
  have hC0 : 0 ≤ C := by rw [hC]; linarith
  refine ⟨C, hC0, ?_⟩
  intro k
  rw [hnorm k]
  by_cases hkM : M ≤ k
  · have hNk : N ≤ k := le_trans (le_max_left _ _) hkM
    have h1k : 1 ≤ k := le_trans (le_max_right _ _) hkM
    calc ‖Qc ^ k‖ ≤ θ ^ k := htail k hNk h1k
      _ = 1 * θ ^ k := (one_mul _).symm
      _ ≤ C * θ ^ k := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [hC]; linarith
  · rw [not_le] at hkM
    have hmem : k ∈ Finset.range M := Finset.mem_range.mpr hkM
    have hterm : ‖Qc ^ k‖ / θ ^ k ≤ C := by
      rw [hC]
      have := Finset.single_le_sum
        (f := fun n => ‖Qc ^ n‖ / θ ^ n)
        (fun n _ => by positivity) hmem
      linarith
    have hθk : 0 < θ ^ k := by positivity
    rw [div_le_iff₀ hθk] at hterm
    exact hterm

/-- The `Matrix (Fin s) (Fin s) ℝ` view of a `ℕ→ℕ→ℝ` matrix (indices `< s`). -/
def toMat (s : ℕ) (Q : ℕ → ℕ → ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  Matrix.of fun a b => Q (a : ℕ) (b : ℕ)

/-- `matPow s Q k i j` agrees with the genuine matrix power on indices `< s`. -/
lemma matPow_eq_toMat_pow (s : ℕ) (Q : ℕ → ℕ → ℝ) (k : ℕ) :
    ∀ (i j : ℕ) (hi : i < s) (hj : j < s),
      matPow s Q k i j = (toMat s Q ^ k) ⟨i, hi⟩ ⟨j, hj⟩ := by
  induction k with
  | zero =>
    intro i j hi hj
    simp only [matPow, pow_zero, Matrix.one_apply, Fin.mk.injEq]
  | succ k ih =>
    intro i j hi hj
    simp only [matPow]
    rw [pow_succ, Matrix.mul_apply]
    rw [← Fin.sum_univ_eq_sum_range (fun l => matPow s Q k i l * Q l j) s]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ih i x hi x.isLt]
    simp only [toMat, Matrix.of_apply]

/-- The row sum `(Qᵏ e)ᵢ` of a nonnegative matrix is bounded by the L∞ operator norm of the
`k`-th power of its `Fin s` view. -/
lemma matVec_matPow_eVec_le_opNorm (s : ℕ) (Q : ℕ → ℕ → ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (k i : ℕ) (hi : i < s) :
    matVec s (matPow s Q k) eVec i ≤ ‖toMat s Q ^ k‖ := by
  simp only [matVec, eVec, mul_one]
  -- rewrite the row sum via the Matrix power and bound by the L∞ operator norm
  have hrewrite : ∑ j ∈ range s, matPow s Q k i j
      = ∑ j : Fin s, (toMat s Q ^ k) ⟨i, hi⟩ j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => matPow s Q k i j) s]
    -- careful: the range-sum uses j < s; convert both to Fin s sums
    apply Finset.sum_congr rfl
    intro x _
    exact matPow_eq_toMat_pow s Q k i x hi x.isLt
  rw [hrewrite]
  -- ∑_j (toMat Q^k) ⟨i⟩ j ≤ ∑_j |(toMat Q^k) ⟨i⟩ j| = row L¹ norm ≤ ‖·‖_{L∞op}
  have hnn : ∀ j : Fin s, 0 ≤ (toMat s Q ^ k) ⟨i, hi⟩ j := by
    intro j
    rw [← matPow_eq_toMat_pow s Q k i j hi j.isLt]
    exact matPow_nonneg s Q hQ k i j
  -- abbreviate the power matrix
  set B : Matrix (Fin s) (Fin s) ℝ := toMat s Q ^ k with hB
  set i₀ : Fin s := ⟨i, hi⟩ with hi₀
  -- the ⟨i⟩-row nnnorm sum is ≤ the sup over rows, which is ‖B‖₊
  have hsup : (∑ j : Fin s, ‖B i₀ j‖₊)
      ≤ (Finset.univ : Finset (Fin s)).sup fun i' => ∑ j : Fin s, ‖B i' j‖₊ :=
    Finset.le_sup (f := fun i' : Fin s => ∑ j : Fin s, ‖B i' j‖₊) (Finset.mem_univ i₀)
  calc ∑ j : Fin s, B i₀ j
      = ∑ j : Fin s, ‖B i₀ j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Real.norm_of_nonneg (hnn j)]
    _ = ((∑ j : Fin s, ‖B i₀ j‖₊ : ℝ≥0) : ℝ) := by push_cast; rfl
    _ ≤ (((Finset.univ : Finset (Fin s)).sup fun i' => ∑ j : Fin s, ‖B i' j‖₊ : ℝ≥0) : ℝ) := by
        exact_mod_cast hsup
    _ = ‖B‖ := by rw [linfty_opNorm_def]

/-- **The convergence input under `ρ(Q) < 1`.**  For a nonnegative `Q` whose `Fin s` view has
complex spectral radius `< 1`, there are `θ < 1` and `C ≥ 0` with `(Qᵏ e)ᵢ ≤ C · θᵏ` for all
`k` and `i < s`.  This is precisely the geometric row-sum decay consumed by the Neumann-series
lemmas of `QSequencePaths.lean`. -/
theorem rowSum_decay_of_spectralRadius (s : ℕ) (Q : ℕ → ℕ → ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hρ : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k := by
  obtain ⟨θ, hθ0, hθ1, C, hC0, hCk⟩ :=
    exists_geometric_bound_of_spectralRadius_lt_one s (toMat s Q) hρ
  refine ⟨θ, hθ0, hθ1, C, hC0, fun k i hi => ?_⟩
  exact le_trans (matVec_matPow_eVec_le_opNorm s Q hQ k i hi) (hCk k)

/-- **Summability of the matrix powers `Aᵏ` under `ρ(A) < 1`.**  The geometric operator-norm
decay `‖Aᵏ‖ ≤ C·θᵏ` makes the power series `Σ Aᵏ` norm-summable, hence summable. -/
lemma summable_pow_of_spectralRadius_lt_one {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ)
    (hρ : spectralRadius ℂ (A.map (algebraMap ℝ ℂ)) < 1) :
    Summable (A ^ ·) := by
  obtain ⟨θ, hθ0, hθ1, C, _hC0, hCk⟩ :=
    exists_geometric_bound_of_spectralRadius_lt_one s A hρ
  refine Summable.of_norm_bounded (g := fun k => C * θ ^ k) ?_ (fun k => hCk k)
  exact (summable_geometric_of_lt_one hθ0 hθ1).mul_left C

/-- **The Neumann series is the inverse: `Σ Aᵏ = (I − A)⁻¹`.**  For a matrix whose complex
spectral radius is `< 1` (so `Σ Aᵏ` converges) and with `I − A` invertible, the sum of the
matrix power series equals the nonsingular inverse of `I − A`. -/
theorem tsum_pow_eq_inv_one_sub {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ)
    (hρ : spectralRadius ℂ (A.map (algebraMap ℝ ℂ)) < 1) :
    (∑' k, A ^ k) = (1 - A)⁻¹ := by
  have hsum : Summable (A ^ ·) := summable_pow_of_spectralRadius_lt_one A hρ
  -- `(1 - A) * Σ Aᵏ = 1`, so `Σ Aᵏ` is the (right) inverse of `1 - A`.
  exact (Matrix.inv_eq_left_inv hsum.tsum_pow_mul_one_sub).symm

/-- The entrywise view of `(I − Q)⁻¹` as a `ℕ → ℕ → ℝ` matrix (indices `< s`; `0` off-block).
This is the same shape as `Nmat`, matching the `rowSum`/`rowSum2` interface. -/
noncomputable def invMat (s : ℕ) (Q : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if h : i < s ∧ j < s then (1 - toMat s Q)⁻¹ ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- **The Neumann series equals the matrix inverse, entrywise.**  For `i, j < s`, the entrywise
Neumann series `Nmat s Q i j = Σ'ₖ (Qᵏ)ᵢⱼ` agrees with the entry `(I − Q)⁻¹ᵢⱼ` of the genuine
matrix inverse, whenever the spectral radius is `< 1`. -/
theorem Nmat_eq_invMat (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hρ : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (i j : ℕ) (hi : i < s) (hj : j < s) :
    Nmat s Q i j = invMat s Q i j := by
  have hsum : Summable ((toMat s Q) ^ ·) := summable_pow_of_spectralRadius_lt_one (toMat s Q) hρ
  -- `Nmat i j = Σ'ₖ (toMat^k) ⟨i⟩⟨j⟩`, then pull the entry evaluation out of the tsum.
  have hNe : Nmat s Q i j = ∑' k, (toMat s Q ^ k) ⟨i, hi⟩ ⟨j, hj⟩ := by
    simp only [Nmat]
    exact tsum_congr fun k => matPow_eq_toMat_pow s Q k i j hi hj
  -- `Σ'ₖ (Mᵏ) i j = (Σ'ₖ Mᵏ) i j` (evaluation is a Pi projection, commuting with `tsum`).
  have hrow : Summable (fun k => (toMat s Q ^ k) ⟨i, hi⟩) := (Pi.summable.mp hsum) ⟨i, hi⟩
  have hentry : ∑' k, (toMat s Q ^ k) ⟨i, hi⟩ ⟨j, hj⟩
      = (1 - toMat s Q)⁻¹ ⟨i, hi⟩ ⟨j, hj⟩ := by
    have h1 : ∑' k, (toMat s Q ^ k) ⟨i, hi⟩ ⟨j, hj⟩
        = (∑' k, (toMat s Q ^ k) ⟨i, hi⟩) ⟨j, hj⟩ := (tsum_apply hrow).symm
    have h2 : (∑' k, (toMat s Q ^ k) ⟨i, hi⟩) = (∑' k, toMat s Q ^ k) ⟨i, hi⟩ :=
      (tsum_apply hsum).symm
    rw [h1, h2, tsum_pow_eq_inv_one_sub (toMat s Q) hρ]
  rw [hNe, hentry, invMat, dif_pos (⟨hi, hj⟩ : i < s ∧ j < s)]

end SSP
