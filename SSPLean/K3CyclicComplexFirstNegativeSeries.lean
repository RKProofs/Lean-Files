import SSPLean.K3CyclicComplexFirstNegativeRecurrence
import SSPLean.K3CyclicComplexFirstNegativeAnalyticODE
import Mathlib.Analysis.Calculus.SmoothSeries

/-! # Analytic realization of the positive complex-first recurrence -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.NegativeCoeff

open scoped BigOperators

noncomputable def tailTerm (r τ : ℝ) (k n : ℕ) (x : ℝ) : ℝ :=
  scalarDerivative r τ (n + 3) * x ^ (n + k) /
    (Nat.factorial (n + k) : ℝ)

noncomputable def tail (r τ : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑' n, tailTerm r τ k n x

noncomputable def recurrenceF (r τ x : ℝ) : ℝ :=
  scalarDerivative r τ 0 + scalarDerivative r τ 1 * x +
    scalarDerivative r τ 2 * x ^ 2 / 2 + tail r τ 3 x

noncomputable def recurrenceF1 (r τ x : ℝ) : ℝ :=
  scalarDerivative r τ 1 + scalarDerivative r τ 2 * x + tail r τ 2 x

noncomputable def recurrenceF2 (r τ x : ℝ) : ℝ :=
  scalarDerivative r τ 2 + tail r τ 1 x

noncomputable def recurrenceF3 (r τ x : ℝ) : ℝ := tail r τ 0 x

theorem tailTerm_hasDerivAt (r τ x : ℝ) (k n : ℕ) :
    HasDerivAt (tailTerm r τ (k + 1) n) (tailTerm r τ k n x) x := by
  have hpow := (hasDerivAt_pow (n + (k + 1)) x).const_mul
    (scalarDerivative r τ (n + 3) /
      (Nat.factorial (n + (k + 1)) : ℝ))
  have hfun : tailTerm r τ (k + 1) n = fun y =>
      (scalarDerivative r τ (n + 3) /
        (Nat.factorial (n + (k + 1)) : ℝ)) * y ^ (n + (k + 1)) := by
    funext y
    unfold tailTerm
    ring
  have hderiv : tailTerm r τ k n x =
      (scalarDerivative r τ (n + 3) /
        (Nat.factorial (n + (k + 1)) : ℝ)) *
          ((n + (k + 1) : ℕ) : ℝ) * x ^ (n + (k + 1) - 1) := by
    unfold tailTerm
    rw [show n + (k + 1) = n + k + 1 by omega,
      show n + k + 1 - 1 = n + k by omega, Nat.factorial_succ]
    push_cast
    field_simp
  rw [hfun, hderiv]
  simpa only [mul_assoc] using hpow

theorem tailTerm_summable
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (k : ℕ) :
    Summable (fun n => tailTerm r τ k n x) := by
  let R : ℝ := max 1 |x|
  let y : ℝ := 3 * R
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := le_max_left _ _
  have hmajorant : Summable (fun n : ℕ =>
      27 * (y ^ (n + k) / (Nat.factorial (n + k) : ℝ))) :=
    ((summable_nat_add_iff k).2 (Real.summable_pow_div_factorial y)).mul_left 27
  apply hmajorant.of_norm_bounded
  intro n
  have hd := abs_scalarDerivative_le_three_pow hr0 hr1 hτ0 hτ1 (n + 3)
  have hthree : (3 : ℝ) ^ (n + 3) ≤ 27 * 3 ^ (n + k) := by
    calc
      (3 : ℝ) ^ (n + 3) = 27 * 3 ^ n := by rw [pow_add]; norm_num; ring
      _ ≤ 27 * 3 ^ (n + k) := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (a := (3 : ℝ)) (by norm_num) (by omega)) (by norm_num)
  have hxpow : |x| ^ (n + k) ≤ R ^ (n + k) :=
    pow_le_pow_left₀ (abs_nonneg x) (le_max_right _ _) _
  unfold tailTerm
  simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs,
    Real.norm_natCast]
  rw [abs_of_nonneg (by positivity : 0 ≤ (Nat.factorial (n + k) : ℝ))]
  rw [show 27 * (y ^ (n + k) / (Nat.factorial (n + k) : ℝ)) =
      (27 * y ^ (n + k)) / (Nat.factorial (n + k) : ℝ) by ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    |scalarDerivative r τ (n + 3)| * |x| ^ (n + k) ≤
        (3 : ℝ) ^ (n + 3) * R ^ (n + k) :=
      mul_le_mul hd hxpow (pow_nonneg (abs_nonneg x) _)
        (pow_nonneg (by norm_num) _)
    _ ≤ (27 * 3 ^ (n + k)) * R ^ (n + k) :=
      mul_le_mul_of_nonneg_right hthree (pow_nonneg hR0 _)
    _ = 27 * y ^ (n + k) := by simp [y, mul_pow]; ring

theorem tailTerm_norm_mono {r τ x B : ℝ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) (k n : ℕ) :
    ‖tailTerm r τ k n x‖ ≤ ‖tailTerm r τ k n B‖ := by
  unfold tailTerm
  simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hB]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg x) hx _)
      (abs_nonneg (scalarDerivative r τ (n + 3)))) (by positivity)

private theorem abs_le_center_add_one {x y : ℝ}
    (hy : y ∈ Set.Ioo (x - 1) (x + 1)) : |y| ≤ |x| + 1 := by
  have hdiff : |y - x| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  calc
    |y| = |x + (y - x)| := by rw [show x + (y - x) = y by ring]
    _ ≤ |x| + |y - x| := abs_add_le _ _
    _ ≤ |x| + 1 := by linarith

theorem tail_hasDerivAt
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (k : ℕ) :
    HasDerivAt (tail r τ (k + 1)) (tail r τ k x) x := by
  let B : ℝ := |x| + 1
  let majorant : ℕ → ℝ := fun n => ‖tailTerm r τ k n B‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmajorant : Summable majorant :=
    (tailTerm_summable hr0 hr1 hτ0 hτ1 k).norm
  have hxmem : x ∈ Set.Ioo (x - 1) (x + 1) := by constructor <;> linarith
  unfold tail
  apply hasDerivAt_tsum_of_isPreconnected hmajorant isOpen_Ioo
    Set.ordConnected_Ioo.isPreconnected
  · intro n y hy
    exact tailTerm_hasDerivAt r τ y k n
  · intro n y hy
    exact tailTerm_norm_mono hB
      (by simpa [B] using abs_le_center_add_one hy) k n
  · exact hxmem
  · exact tailTerm_summable hr0 hr1 hτ0 hτ1 (k + 1)
  · exact hxmem

theorem recurrenceF_hasDerivAt
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    HasDerivAt (recurrenceF r τ) (recurrenceF1 r τ x) x := by
  unfold recurrenceF recurrenceF1
  convert! (((hasDerivAt_const x (scalarDerivative r τ 0)).add
    ((hasDerivAt_id x).const_mul (scalarDerivative r τ 1))).add
      ((hasDerivAt_pow 2 x).const_mul (scalarDerivative r τ 2 / 2))).add
        (tail_hasDerivAt hr0 hr1 hτ0 hτ1 2) using 1
  · funext y
    simp only [Pi.add_apply, id_eq]
    ring
  · norm_num
    ring

theorem recurrenceF1_hasDerivAt
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    HasDerivAt (recurrenceF1 r τ) (recurrenceF2 r τ x) x := by
  unfold recurrenceF1 recurrenceF2
  convert! ((hasDerivAt_const x (scalarDerivative r τ 1)).add
    ((hasDerivAt_id x).const_mul (scalarDerivative r τ 2))).add
      (tail_hasDerivAt hr0 hr1 hτ0 hτ1 1) using 1
  all_goals ring

theorem recurrenceF2_hasDerivAt
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    HasDerivAt (recurrenceF2 r τ) (recurrenceF3 r τ x) x := by
  unfold recurrenceF2 recurrenceF3
  convert! (hasDerivAt_const x (scalarDerivative r τ 2)).add
    (tail_hasDerivAt hr0 hr1 hτ0 hτ1 0) using 1
  all_goals ring

/-- The recurrence series satisfies the same cubic ODE as the normalized
analytic function. -/
theorem recurrenceF_cubic_ode
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    recurrenceF3 r τ x = scalarTrace r * recurrenceF2 r τ x -
      scalarPair r τ * recurrenceF1 r τ x +
        scalarFeedback r τ * recurrenceF r τ x := by
  let f0 : ℕ → ℝ := fun n => tailTerm r τ 0 n x
  let f1 : ℕ → ℝ := fun n => tailTerm r τ 1 n x
  let f2 : ℕ → ℝ := fun n => tailTerm r τ 2 n x
  let f3 : ℕ → ℝ := fun n => tailTerm r τ 3 n x
  have h0 : Summable f0 := tailTerm_summable hr0 hr1 hτ0 hτ1 0
  have h1 : Summable f1 := tailTerm_summable hr0 hr1 hτ0 hτ1 1
  have h2 : Summable f2 := tailTerm_summable hr0 hr1 hτ0 hτ1 2
  have h3 : Summable f3 := tailTerm_summable hr0 hr1 hτ0 hτ1 3
  have hpoint : ∀ n,
      f0 (n + 3) = scalarTrace r * f1 (n + 2) -
        scalarPair r τ * f2 (n + 1) + scalarFeedback r τ * f3 n := by
    intro n
    dsimp [f0, f1, f2, f3]
    unfold tailTerm
    rw [show n + 3 + 3 = (n + 3) + 3 by omega, scalarDerivative]
    norm_num
    ring
  have h1shift : Summable (fun n => f1 (n + 2)) :=
    (summable_nat_add_iff 2).2 h1
  have h2shift : Summable (fun n => f2 (n + 1)) :=
    (summable_nat_add_iff 1).2 h2
  have h0split := h0.sum_add_tsum_nat_add 3
  have h1split := h1.sum_add_tsum_nat_add 2
  have h2split := h2.sum_add_tsum_nat_add 1
  have htail :
      (∑' n, f0 (n + 3)) =
        scalarTrace r * (∑' n, f1 (n + 2)) -
          scalarPair r τ * (∑' n, f2 (n + 1)) +
            scalarFeedback r τ * (∑' n, f3 n) := by
    rw [tsum_congr hpoint]
    exact (((h1shift.hasSum.mul_left (scalarTrace r)).sub
      (h2shift.hasSum.mul_left (scalarPair r τ))).add
        (h3.hasSum.mul_left (scalarFeedback r τ))).tsum_eq
  unfold recurrenceF recurrenceF1 recurrenceF2 recurrenceF3 tail
  change (∑' n, f0 n) =
    scalarTrace r * (scalarDerivative r τ 2 + ∑' n, f1 n) -
      scalarPair r τ *
        (scalarDerivative r τ 1 + scalarDerivative r τ 2 * x +
          ∑' n, f2 n) +
      scalarFeedback r τ *
        (scalarDerivative r τ 0 + scalarDerivative r τ 1 * x +
          scalarDerivative r τ 2 * x ^ 2 / 2 + ∑' n, f3 n)
  rw [← h0split, ← h1split, ← h2split, htail]
  dsimp [f0, f1, f2, f3]
  norm_num [tailTerm, scalarDerivative, Finset.sum_range_succ]
  ring

@[simp] theorem recurrenceF_zero (r τ : ℝ) : recurrenceF r τ 0 = 1 := by
  unfold recurrenceF tail
  simp [tailTerm, scalarDerivative]

@[simp] theorem recurrenceF1_zero (r τ : ℝ) :
    recurrenceF1 r τ 0 = 0 := by
  unfold recurrenceF1 tail
  simp [tailTerm, scalarDerivative]

@[simp] theorem recurrenceF2_zero (r τ : ℝ) :
    recurrenceF2 r τ 0 = 0 := by
  unfold recurrenceF2 tail
  simp [tailTerm, scalarDerivative]

/-- The executable recurrence series is the normalized analytic first-start
function throughout the negative chart. -/
theorem recurrenceF_eq_shiftedFirstF
    {m₀ ω r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hr : r = -3 * m₀) (hz : scalarZ r τ = ω ^ 2) (hω : ω ≠ 0) :
    recurrenceF r τ = shiftedFirstF m₀ ω := by
  have htrace : scalarTrace r = 1 + 3 * m₀ := by
    rw [hr]
    unfold scalarTrace
    ring
  have hz' : scalarZ (-3 * m₀) τ = ω ^ 2 := by simpa [hr] using hz
  have hpair : scalarPair r τ = 3 * m₀ ^ 2 + 2 * m₀ + ω ^ 2 := by
    rw [hr]
    unfold scalarPair
    rw [hz']
    ring
  have hfeedback : scalarFeedback r τ =
      (1 + m₀) * (m₀ ^ 2 + ω ^ 2) := by
    rw [hr]
    unfold scalarFeedback
    rw [hz']
    ring
  have hseries2 : ∀ x, HasDerivAt (recurrenceF2 r τ)
      (scalarFeedback r τ * recurrenceF r τ x -
        scalarPair r τ * recurrenceF1 r τ x +
        scalarTrace r * recurrenceF2 r τ x) x := by
    intro x
    convert! recurrenceF2_hasDerivAt hr0 hr1 hτ0 hτ1 using 1
    rw [recurrenceF_cubic_ode hr0 hr1 hτ0 hτ1]
    ring
  have hanalytic2 : ∀ x, HasDerivAt (shiftedFirstF2 m₀ ω)
      (scalarFeedback r τ * shiftedFirstF m₀ ω x -
        scalarPair r τ * shiftedFirstF1 m₀ ω x +
        scalarTrace r * shiftedFirstF2 m₀ ω x) x := by
    intro x
    convert! shiftedFirstF2_hasDerivAt
      (m := m₀) (ω := ω) (x := x) hω using 1
    rw [shiftedFirstF_cubic_ode, htrace, hpair, hfeedback]
    ring
  apply SSP.CubicODE.eq_of_cubic_ode
    (c0 := scalarFeedback r τ) (c1 := -scalarPair r τ)
    (c2 := scalarTrace r) (t0 := 0)
    (fun x => recurrenceF_hasDerivAt hr0 hr1 hτ0 hτ1)
    (fun x => recurrenceF1_hasDerivAt hr0 hr1 hτ0 hτ1)
    (fun x => by convert hseries2 x using 1 <;> ring)
    (fun x => shiftedFirstF_hasDerivAt (m := m₀) (ω := ω) (x := x) hω)
    (fun x => shiftedFirstF1_hasDerivAt (m := m₀) (ω := ω) (x := x) hω)
    (fun x => by convert hanalytic2 x using 1 <;> ring)
  · simp
  · simp
  · simp

/-! ## Ordinary exponential-generating-series form -/

noncomputable def egfTerm (r τ : ℝ) (shift n : ℕ) (x : ℝ) : ℝ :=
  scalarDerivative r τ (n + shift) * x ^ n / (Nat.factorial n : ℝ)

theorem egfTerm_summable
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (shift : ℕ) :
    Summable (fun n => egfTerm r τ shift n x) := by
  let R : ℝ := max 1 |x|
  let y : ℝ := 3 * R
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hmajorant : Summable (fun n : ℕ =>
      (3 : ℝ) ^ shift * (y ^ n / (Nat.factorial n : ℝ))) :=
    (Real.summable_pow_div_factorial y).mul_left ((3 : ℝ) ^ shift)
  apply hmajorant.of_norm_bounded
  intro n
  have hd := abs_scalarDerivative_le_three_pow hr0 hr1 hτ0 hτ1 (n + shift)
  have hxpow : |x| ^ n ≤ R ^ n :=
    pow_le_pow_left₀ (abs_nonneg x) (le_max_right _ _) _
  unfold egfTerm
  simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : 0 ≤ (Nat.factorial n : ℝ))]
  rw [show (3 : ℝ) ^ shift * (y ^ n / (Nat.factorial n : ℝ)) =
      (3 ^ shift * y ^ n) / (Nat.factorial n : ℝ) by ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    |scalarDerivative r τ (n + shift)| * |x| ^ n ≤
        (3 : ℝ) ^ (n + shift) * R ^ n :=
      mul_le_mul hd hxpow (pow_nonneg (abs_nonneg x) _)
        (pow_nonneg (by norm_num) _)
    _ = 3 ^ shift * y ^ n := by simp [pow_add, y, mul_pow]; ring

theorem recurrenceF_eq_egf
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    recurrenceF r τ x = ∑' n, egfTerm r τ 0 n x := by
  let f : ℕ → ℝ := fun n => egfTerm r τ 0 n x
  have hf : Summable f := egfTerm_summable hr0 hr1 hτ0 hτ1 0
  have hsplit := hf.sum_add_tsum_nat_add 3
  rw [← hsplit]
  unfold recurrenceF tail
  change _ = (∑ n ∈ Finset.range 3, f n) + ∑' n, f (n + 3)
  have htail : (fun n => f (n + 3)) = fun n => tailTerm r τ 3 n x := by
    funext n
    simp [f, egfTerm, tailTerm]
  rw [htail]
  dsimp [f]
  norm_num [egfTerm, scalarDerivative, Finset.sum_range_succ]

theorem recurrenceF1_eq_egf
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    recurrenceF1 r τ x = ∑' n, egfTerm r τ 1 n x := by
  let f : ℕ → ℝ := fun n => egfTerm r τ 1 n x
  have hf : Summable f := egfTerm_summable hr0 hr1 hτ0 hτ1 1
  have hsplit := hf.sum_add_tsum_nat_add 2
  rw [← hsplit]
  unfold recurrenceF1 tail
  change _ = (∑ n ∈ Finset.range 2, f n) + ∑' n, f (n + 2)
  have htail : (fun n => f (n + 2)) = fun n => tailTerm r τ 2 n x := by
    funext n
    simp [f, egfTerm, tailTerm]
  rw [htail]
  dsimp [f]
  norm_num [egfTerm, scalarDerivative, Finset.sum_range_succ]

theorem recurrenceF2_eq_egf
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    recurrenceF2 r τ x = ∑' n, egfTerm r τ 2 n x := by
  let f : ℕ → ℝ := fun n => egfTerm r τ 2 n x
  have hf : Summable f := egfTerm_summable hr0 hr1 hτ0 hτ1 2
  have hsplit := hf.sum_add_tsum_nat_add 1
  rw [← hsplit]
  unfold recurrenceF2 tail
  change _ = (∑ n ∈ Finset.range 1, f n) + ∑' n, f (n + 1)
  have htail : (fun n => f (n + 1)) = fun n => tailTerm r τ 1 n x := by
    funext n
    simp [f, egfTerm, tailTerm]
  rw [htail]
  dsimp [f]
  norm_num [egfTerm, scalarDerivative, Finset.sum_range_succ]

end SSP.K3CyclicComplex.NegativeCoeff
