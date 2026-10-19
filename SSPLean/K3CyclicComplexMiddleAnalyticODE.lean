import SSPLean.K3CyclicComplexMiddleCurvatureSeries
import Mathlib.Analysis.Calculus.SmoothSeries

/-! # Differential equations for the complex-middle EGF -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

noncomputable def middleEgfTail
    (rhoValue etaValue : ℝ) (shift : ℕ) (x : ℝ) : ℝ :=
  ∑' n, middleEgfTerm rhoValue etaValue shift (n + 1) x

lemma middleEgfTerm_succ_hasDerivAt
    (rhoValue etaValue x : ℝ) (shift n : ℕ) :
    HasDerivAt (middleEgfTerm rhoValue etaValue shift (n + 1))
      (middleEgfTerm rhoValue etaValue (shift + 1) n x) x := by
  have hpow := (hasDerivAt_pow (n + 1) x).const_mul
    (scalarDerivative rhoValue etaValue (n + 1 + shift) /
      (Nat.factorial (n + 1) : ℝ))
  have hfun : middleEgfTerm rhoValue etaValue shift (n + 1) = fun y =>
      (scalarDerivative rhoValue etaValue (n + 1 + shift) /
        (Nat.factorial (n + 1) : ℝ)) * y ^ (n + 1) := by
    funext y
    unfold middleEgfTerm
    ring
  have hderiv : middleEgfTerm rhoValue etaValue (shift + 1) n x =
      (scalarDerivative rhoValue etaValue (n + 1 + shift) /
        (Nat.factorial (n + 1) : ℝ)) *
          ((n + 1 : ℕ) : ℝ) * x ^ (n + 1 - 1) := by
    unfold middleEgfTerm
    rw [show n + (shift + 1) = n + 1 + shift by omega,
      show n + 1 - 1 = n by omega, Nat.factorial_succ]
    push_cast
    field_simp
  rw [hfun, hderiv]
  simpa only [mul_assoc] using hpow

private theorem abs_le_center_add_one {x y : ℝ}
    (hy : y ∈ Set.Ioo (x - 1) (x + 1)) : |y| ≤ |x| + 1 := by
  have hdiff : |y - x| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  calc
    |y| = |x + (y - x)| := by rw [show x + (y - x) = y by ring]
    _ ≤ |x| + |y - x| := abs_add_le _ _
    _ ≤ |x| + 1 := by linarith

lemma middleEgfTerm_norm_mono
    {rhoValue etaValue x B : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ B)
    (shift n : ℕ) :
    ‖middleEgfTerm rhoValue etaValue shift n x‖ ≤
      ‖middleEgfTerm rhoValue etaValue shift n B‖ := by
  unfold middleEgfTerm
  simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hB]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg x) hx _)
      (abs_nonneg (scalarDerivative rhoValue etaValue (n + shift))))
    (by positivity)

theorem middleEgfTail_hasDerivAt
    {rhoValue etaValue x : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) (shift : ℕ) :
    HasDerivAt (middleEgfTail rhoValue etaValue shift)
      (middleEgf rhoValue etaValue (shift + 1) x) x := by
  let B : ℝ := |x| + 1
  let majorant : ℕ → ℝ := fun n =>
    ‖middleEgfTerm rhoValue etaValue (shift + 1) n B‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmajorant : Summable majorant :=
    (middleEgfTerm_summable (x := B)
      hrho0 hrho1 heta0 heta1 (shift + 1)).norm
  have hxmem : x ∈ Set.Ioo (x - 1) (x + 1) := by
    constructor <;> linarith
  unfold middleEgfTail middleEgf
  apply hasDerivAt_tsum_of_isPreconnected hmajorant isOpen_Ioo
    Set.ordConnected_Ioo.isPreconnected
  · intro n y hy
    exact middleEgfTerm_succ_hasDerivAt rhoValue etaValue y shift n
  · intro n y hy
    exact middleEgfTerm_norm_mono hB
      (by simpa [B] using abs_le_center_add_one hy) (shift + 1) n
  · exact hxmem
  · have hs := middleEgfTerm_summable
      (x := x) hrho0 hrho1 heta0 heta1 shift
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      ((summable_nat_add_iff 1).2 hs)
  · exact hxmem

lemma middleEgf_eq_const_add_tail
    {rhoValue etaValue x : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) (shift : ℕ) :
    middleEgf rhoValue etaValue shift x =
      scalarDerivative rhoValue etaValue shift +
        middleEgfTail rhoValue etaValue shift x := by
  have hs := middleEgfTerm_summable
    (x := x) hrho0 hrho1 heta0 heta1 shift
  have hsplit := hs.sum_add_tsum_nat_add 1
  unfold middleEgf middleEgfTail
  rw [← hsplit]
  norm_num [middleEgfTerm]

theorem middleEgf_hasDerivAt
    {rhoValue etaValue x : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) (shift : ℕ) :
    HasDerivAt (middleEgf rhoValue etaValue shift)
      (middleEgf rhoValue etaValue (shift + 1) x) x := by
  have hfun : middleEgf rhoValue etaValue shift = fun y =>
      scalarDerivative rhoValue etaValue shift +
        middleEgfTail rhoValue etaValue shift y := by
    funext y
    exact middleEgf_eq_const_add_tail
      hrho0 hrho1 heta0 heta1 shift
  rw [hfun]
  have h :=
    (hasDerivAt_const x (scalarDerivative rhoValue etaValue shift)).add
      (middleEgfTail_hasDerivAt hrho0 hrho1 heta0 heta1 shift)
  convert h using 1
  · rfl
  · rfl
  · rfl
  · simp

lemma scalarDerivative_eq_A_add_oscillation
    (rhoValue etaValue : ℝ) (n : ℕ) :
    scalarDerivative rhoValue etaValue n =
      scalarA rhoValue etaValue +
        oscillationReal (scalarA rhoValue etaValue)
          (scalarB rhoValue etaValue) (scalarZ rhoValue) n := by
  unfold scalarDerivative oscillationReal cosineTerm sineTerm
  ring

theorem scalarDerivative_cubic_recurrence
    (rhoValue etaValue : ℝ) (n : ℕ) :
    scalarDerivative rhoValue etaValue (n + 3) =
      scalarDerivative rhoValue etaValue (n + 2) -
        scalarZ rhoValue * scalarDerivative rhoValue etaValue (n + 1) +
        scalarZ rhoValue * scalarDerivative rhoValue etaValue n := by
  simp_rw [scalarDerivative_eq_A_add_oscillation]
  rw [show n + 3 = (n + 1) + 2 by omega,
    oscillationReal_add_two,
    oscillationReal_add_two (scalarA rhoValue etaValue)
      (scalarB rhoValue etaValue) (scalarZ rhoValue) n]
  ring

theorem middleEgf_cubic_ode
    {rhoValue etaValue x : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) :
    middleEgf rhoValue etaValue 3 x =
      middleEgf rhoValue etaValue 2 x -
        scalarZ rhoValue * middleEgf rhoValue etaValue 1 x +
        scalarZ rhoValue * middleEgf rhoValue etaValue 0 x := by
  have h3 := middleEgfTerm_summable
    (x := x) hrho0 hrho1 heta0 heta1 3
  have h2 := middleEgfTerm_summable
    (x := x) hrho0 hrho1 heta0 heta1 2
  have h1 := middleEgfTerm_summable
    (x := x) hrho0 hrho1 heta0 heta1 1
  have h0 := middleEgfTerm_summable
    (x := x) hrho0 hrho1 heta0 heta1 0
  have hsum := (h2.hasSum.sub
    (h1.hasSum.mul_left (scalarZ rhoValue))).add
      (h0.hasSum.mul_left (scalarZ rhoValue))
  unfold middleEgf
  rw [← hsum.tsum_eq]
  apply tsum_congr
  intro n
  unfold middleEgfTerm
  rw [scalarDerivative_cubic_recurrence rhoValue etaValue n]
  ring_nf

@[simp] theorem middleEgf_zero
    {rhoValue etaValue : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) (shift : ℕ) :
    middleEgf rhoValue etaValue shift 0 =
      scalarDerivative rhoValue etaValue shift := by
  rw [middleEgf_eq_const_add_tail hrho0 hrho1 heta0 heta1 shift]
  simp [middleEgfTail, middleEgfTerm]

theorem middleEgf_curvature_nonneg
    {rhoValue etaValue x : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1)
    (hx : 0 ≤ x) :
    0 ≤ x ^ 2 *
        (middleEgf rhoValue etaValue 0 x *
            middleEgf rhoValue etaValue 2 x -
          middleEgf rhoValue etaValue 1 x ^ 2) +
      middleEgf rhoValue etaValue 0 x ^ 2 := by
  exact middleRecurrenceCurvature_nonneg
    hrho0 hrho1 heta0 heta1 hx

theorem middleEgf_derivative_curvature_nonneg
    {rhoValue etaValue x : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1)
    (hx : 0 ≤ x) :
    0 ≤ x ^ 2 *
        (middleEgf rhoValue etaValue 0 x *
            deriv (fun y => deriv (middleEgf rhoValue etaValue 0) y) x -
          deriv (middleEgf rhoValue etaValue 0) x ^ 2) +
      middleEgf rhoValue etaValue 0 x ^ 2 := by
  rw [(middleEgf_hasDerivAt hrho0 hrho1 heta0 heta1 0).deriv]
  have hfun : deriv (middleEgf rhoValue etaValue 0) =
      middleEgf rhoValue etaValue 1 := by
    funext y
    exact (middleEgf_hasDerivAt hrho0 hrho1 heta0 heta1 0).deriv
  rw [hfun, (middleEgf_hasDerivAt hrho0 hrho1 heta0 heta1 1).deriv]
  exact middleEgf_curvature_nonneg hrho0 hrho1 heta0 heta1 hx

end SSP.K3CyclicComplex.MiddleCoeff
