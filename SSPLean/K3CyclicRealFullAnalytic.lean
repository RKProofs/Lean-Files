import SSPLean.K3CyclicRealFullComplete
import SSPLean.K3CyclicCurvatureInvariance

/-! Analytic assembly of the full real-root first-start curvature. -/

set_option autoImplicit false

namespace SSP.K3CyclicRealTail

open scoped BigOperators

noncomputable def fullCurvatureSeriesTerm
    (u v t : ℝ) (M : ℕ) : ℝ :=
  fullCurvatureCoefficient u v M * t ^ (M + 6) /
    (Nat.factorial (M + 6) : ℝ)

theorem fullCurvatureSeriesTerm_eq (u v t : ℝ) (M : ℕ) :
    fullCurvatureSeriesTerm u v t M =
      (u * v) ^ 2 * varianceSeriesTerm u v t M +
        t ^ 2 * completeTaylorTerm u v 1 (M + 3) t +
        4 * completeTaylorTerm u v 3 (M + 3) t := by
  unfold fullCurvatureSeriesTerm fullCurvatureCoefficient varianceSeriesTerm
    completeTaylorTerm
  rw [show M + 3 + 1 = M + 4 by omega,
    show M + 3 + 3 = M + 6 by omega,
    show M + 6 = (M + 4) + 2 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem fullCurvatureSeriesTerm_summable
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Summable (fullCurvatureSeriesTerm u v t) := by
  have hvsum := varianceSeriesTerm_summable hu0 hu1 hv0 hv1 (t := t)
  have h1 := (summable_nat_add_iff 3).2
    (completeTaylorTerm_summable hu0 hu1 hv0 hv1
      (t := t) (k := 1) (by omega))
  have h3 := (summable_nat_add_iff 3).2
    (completeTaylorTerm_summable hu0 hu1 hv0 hv1
      (t := t) (k := 3) (by omega))
  apply Summable.congr
    (((hvsum.mul_left ((u * v) ^ 2)).add
      (h1.mul_left (t ^ 2))).add (h3.mul_left 4))
  intro M
  exact (fullCurvatureSeriesTerm_eq u v t M).symm

theorem fullCurvatureSeries_nonneg_of_root
    {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) (ht : 0 ≤ t) :
    0 ≤ ∑' M, fullCurvatureSeriesTerm u v t M := by
  apply tsum_nonneg
  intro M
  unfold fullCurvatureSeriesTerm
  exact div_nonneg
    (mul_nonneg (fullCurvatureCoefficient_nonneg_of_root hu hv hroot M)
      (pow_nonneg ht _)) (by positivity)

theorem firstStartCurvature_eq_fullSeries
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    t ^ 2 *
        ((1 + firstStartRemainder u v t) *
            deriv (fun x => deriv (firstStartRemainder u v) x) t -
          deriv (firstStartRemainder u v) t ^ 2) +
      2 * (1 + firstStartRemainder u v t) ^ 2 =
      2 + (∑ n ∈ Finset.range 3,
        (t ^ 2 * completeTaylorTerm u v 1 n t +
          4 * completeTaylorTerm u v 3 n t)) +
        ∑' M, fullCurvatureSeriesTerm u v t M := by
  let lin : ℕ → ℝ := fun n =>
    t ^ 2 * completeTaylorTerm u v 1 n t +
      4 * completeTaylorTerm u v 3 n t
  have hvsum := varianceSeriesTerm_summable hu0 hu1 hv0 hv1 (t := t)
  have h1 := completeTaylorTerm_summable hu0 hu1 hv0 hv1
    (t := t) (k := 1) (by omega)
  have h3 := completeTaylorTerm_summable hu0 hu1 hv0 hv1
    (t := t) (k := 3) (by omega)
  have hlin : Summable lin := (h1.mul_left (t ^ 2)).add (h3.mul_left 4)
  have hlinSum : (∑' n, lin n) =
      t ^ 2 * (∑' n, completeTaylorTerm u v 1 n t) +
        4 * (∑' n, completeTaylorTerm u v 3 n t) := by
    exact ((h1.hasSum.mul_left (t ^ 2)).add
      (h3.hasSum.mul_left 4)).tsum_eq
  have hlinSplit := hlin.sum_add_tsum_nat_add 3
  have hcombine :
      t ^ 2 * (∑' n, completeTaylorTerm u v 1 n t) +
          4 * (∑' n, completeTaylorTerm u v 3 n t) =
        (∑ n ∈ Finset.range 3, lin n) + ∑' n, lin (n + 3) := by
    rw [← hlinSum, ← hlinSplit]
  have hshift : Summable (fun M => lin (M + 3)) :=
    (summable_nat_add_iff 3).2 hlin
  have hfull : HasSum (fullCurvatureSeriesTerm u v t)
      ((u * v) ^ 2 * (∑' M, varianceSeriesTerm u v t M) +
        ∑' M, lin (M + 3)) := by
    rw [show fullCurvatureSeriesTerm u v t = fun M =>
        (u * v) ^ 2 * varianceSeriesTerm u v t M + lin (M + 3) by
      funext M
      simpa [lin, add_assoc] using fullCurvatureSeriesTerm_eq u v t M]
    exact (hvsum.hasSum.mul_left ((u * v) ^ 2)).add hshift.hasSum
  calc
    _ = firstStartRemainderCurvature u v t +
          t ^ 2 * firstStartRemainderDeriv2 u v t +
          4 * firstStartRemainder u v t + 2 := by
      unfold firstStartRemainderCurvature
      rw [firstStartRemainder_deriv_eq hu0 hu1 hv0 hv1,
        firstStartRemainder_second_deriv_eq hu0 hu1 hv0 hv1]
      ring
    _ = varianceCurvatureSeries u v t +
          t ^ 2 * firstStartRemainderDeriv2 u v t +
          4 * firstStartRemainder u v t + 2 := by
      rw [firstStartRemainderCurvature_eq_varianceCurvatureSeries
        hu0 hu1 hv0 hv1]
    _ = 2 + (∑ n ∈ Finset.range 3,
          (t ^ 2 * completeTaylorTerm u v 1 n t +
            4 * completeTaylorTerm u v 3 n t)) +
          ∑' M, fullCurvatureSeriesTerm u v t M := by
      unfold varianceCurvatureSeries firstStartRemainderDeriv2
        firstStartRemainder
      rw [hfull.tsum_eq]
      change _ = 2 + (∑ n ∈ Finset.range 3, lin n) + _
      linarith [hcombine]

theorem firstStartCurvature_nonneg_of_root_all_time
    {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) (ht : 0 ≤ t) :
    0 ≤ t ^ 2 *
        ((1 + firstStartRemainder u v t) *
            deriv (fun x => deriv (firstStartRemainder u v) x) t -
          deriv (firstStartRemainder u v) t ^ 2) +
      2 * (1 + firstStartRemainder u v t) ^ 2 := by
  have hsu : Real.sqrt u ≤ 1 := by nlinarith [Real.sqrt_nonneg v]
  have hsv : Real.sqrt v ≤ 1 := by nlinarith [Real.sqrt_nonneg u]
  have hu1 : u ≤ 1 := by
    nlinarith [Real.sq_sqrt hu, Real.sqrt_nonneg u]
  have hv1 : v ≤ 1 := by
    nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v]
  rw [firstStartCurvature_eq_fullSeries hu hu1 hv hv1]
  apply add_nonneg (add_nonneg (by norm_num) ?_)
    (fullCurvatureSeries_nonneg_of_root hu hv hroot ht)
  apply Finset.sum_nonneg
  intro n hn
  exact add_nonneg
    (mul_nonneg (sq_nonneg t) (completeTaylorTerm_nonneg hu hv ht 1 n))
    (mul_nonneg (by norm_num) (completeTaylorTerm_nonneg hu hv ht 3 n))

open SSP.K3Cyclic in
theorem normalizedFirstStart_correctedCurvature3_nonneg
    {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) (ht : 0 ≤ t) :
    0 ≤ correctedCurvature3 t
      (1 + firstStartRemainder u v t)
      (deriv (firstStartRemainder u v) t)
      (deriv (fun x => deriv (firstStartRemainder u v) x) t) := by
  unfold correctedCurvature3
  exact firstStartCurvature_nonneg_of_root_all_time hu hv hroot ht

end SSP.K3CyclicRealTail
