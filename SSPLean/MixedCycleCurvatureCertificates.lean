import SSPLean.FourCycleCurvatureAlgebra
import Mathlib.Analysis.Complex.Exponential

/-! # Finite and tail certificates for a mixed three/four-cycle family

These are the exact arithmetic certificates in `s4_mixed_feedback_proof.md`.
Modes 0--3 represent `J₀,...,J₃`; mode 4 represents the last diagonal kernel `K`.
The finite check is only through degree 48. The written proof combines it with
an infinite Taylor remainder bound and a spectral tail estimate; this module
does not yet formalize that analytic assembly or prove the general s=4 case.

`Nat.fast_choose` evaluates binomial coefficients by factorial division rather
than Pascal recursion. All finite checks use kernel `decide`, not native code.
-/

set_option autoImplicit false

namespace SSP.MixedCycle

def residue (mode : ℕ) : ℕ := if mode < 4 then mode else 0

def loopWeight (mode m n : ℕ) : ℕ :=
  if mode < 4 then Nat.fast_choose (m + n) m
  else if n = 0 then if m = 0 then 1 else 0
  else Nat.fast_choose (m + n - 1) m

theorem loopWeight_eq_choose (mode m n : ℕ) :
    loopWeight mode m n =
      if mode < 4 then (m + n).choose m
      else if n = 0 then if m = 0 then 1 else 0
      else (m + n - 1).choose m := by
  simp only [loopWeight, Nat.choose_eq_fast_choose]

def degree (mode M N : ℕ) : ℕ := 3 * M + 4 * N + 2 * residue mode

/-- The coefficient of `a^M b^N t^L` is this integer divided by `2 * L!`. -/
def twiceCoefficientNumerator (mode M N : ℕ) : ℤ :=
  let L := degree mode M N
  ((List.range (M + 1)).map fun m =>
    ((List.range (N + 1)).map fun n =>
      let j := 3 * m + 4 * n + residue mode
      (Nat.fast_choose L j : ℤ) * loopWeight mode m n *
        loopWeight mode (M - m) (N - n) *
        ((2 * (j : ℤ) - (L : ℤ)) ^ 2 - (L : ℤ) + 6)).sum).sum

def certificateAt (mode M N : ℕ) : Prop :=
  if degree mode M N ≤ 48 then
    if (mode = 0 ∨ mode = 4) ∧ M = 0 ∧ N = 2 then
      twiceCoefficientNumerator mode M N = -16
    else 0 ≤ twiceCoefficientNumerator mode M N
  else True

instance (mode M N : ℕ) : Decidable (certificateAt mode M N) :=
  inferInstanceAs (Decidable (if degree mode M N ≤ 48 then
    if (mode = 0 ∨ mode = 4) ∧ M = 0 ∧ N = 2 then
      twiceCoefficientNumerator mode M N = -16
    else 0 ≤ twiceCoefficientNumerator mode M N
  else True))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem finiteCertificate_J0 :
    ∀ M : Fin 17, ∀ N : Fin 13, certificateAt 0 M N := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem finiteCertificate_J1 :
    ∀ M : Fin 17, ∀ N : Fin 13, certificateAt 1 M N := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem finiteCertificate_J2 :
    ∀ M : Fin 17, ∀ N : Fin 13, certificateAt 2 M N := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem finiteCertificate_J3 :
    ∀ M : Fin 17, ∀ N : Fin 13, certificateAt 3 M N := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem finiteCertificate_K :
    ∀ M : Fin 17, ∀ N : Fin 13, certificateAt 4 M N := by
  decide

/-- Every degree through 48 is covered; larger natural indices are excluded
by the degree bound, rather than omitted by an arbitrary rectangle. -/
theorem finiteCertificate (mode M N : ℕ) (hmode : mode ≤ 4)
    (hdegree : degree mode M N ≤ 48) :
    if (mode = 0 ∨ mode = 4) ∧ M = 0 ∧ N = 2 then
      twiceCoefficientNumerator mode M N = -16
    else 0 ≤ twiceCoefficientNumerator mode M N := by
  have hb : M < 17 ∧ N < 13 := by
    unfold degree at hdegree
    omega
  have h : certificateAt mode M N := by
    have hm : mode = 0 ∨ mode = 1 ∨ mode = 2 ∨ mode = 3 ∨ mode = 4 := by omega
    rcases hm with h | h | h | h | h <;> subst mode
    · exact finiteCertificate_J0 ⟨M, hb.1⟩ ⟨N, hb.2⟩
    · exact finiteCertificate_J1 ⟨M, hb.1⟩ ⟨N, hb.2⟩
    · exact finiteCertificate_J2 ⟨M, hb.1⟩ ⟨N, hb.2⟩
    · exact finiteCertificate_J3 ⟨M, hb.1⟩ ⟨N, hb.2⟩
    · exact finiteCertificate_K ⟨M, hb.1⟩ ⟨N, hb.2⟩
  simpa only [certificateAt, if_pos hdegree] using h

/-- Integers underlying the retained terms in the near-zero lower bounds. -/
theorem retainedCoefficientTable :
    [twiceCoefficientNumerator 0 0 0, twiceCoefficientNumerator 0 0 1,
     twiceCoefficientNumerator 0 0 2, twiceCoefficientNumerator 0 0 3,
     twiceCoefficientNumerator 4 0 0, twiceCoefficientNumerator 4 0 1,
     twiceCoefficientNumerator 4 0 2, twiceCoefficientNumerator 4 0 3,
     twiceCoefficientNumerator 1 0 0, twiceCoefficientNumerator 2 0 0,
     twiceCoefficientNumerator 3 1 0, twiceCoefficientNumerator 3 0 1] =
      [6, 36, -16, 10176, 6, 36, -16, 10176, 8, 12, 1008, 2880] := by
  decide

/-- The geometric remainder constant is strictly below one billionth. -/
theorem remainderConstant_integer :
    2358 * 2 ^ 166 * 10 ^ 9 < Nat.factorial 49 := by
  decide

theorem nearZeroMargins :
    (8 : ℕ) ^ 10 < 3 * 10 ^ 9 ∧
    (8 : ℕ) ^ 8 < 2 * 10 ^ 9 ∧
    4 * (8 : ℕ) ^ 6 < 10 ^ 9 ∧ 5760 < (10 : ℕ) ^ 9 := by
  decide

theorem remainderRatio_identity (y : ℝ) :
    (49 + y) ^ 3 - 32 * (49 + y) ^ 2 - 27 * (49 + y) - 186 =
      y ^ 3 + 115 * y ^ 2 + 4040 * y + 39308 := by
  ring

theorem remainderRatio_nonneg (L : ℝ) (hL : 49 ≤ L) :
    0 ≤ L ^ 3 - 32 * L ^ 2 - 27 * L - 186 := by
  have hy : 0 ≤ L - 49 := by linarith
  have heq : L = 49 + (L - 49) := by ring
  rw [heq, remainderRatio_identity]
  positivity

/-- This is precisely twice the numerator of the consecutive-term ratio. -/
theorem remainderRatio_bound (L : ℝ) (hL : 49 ≤ L) :
    32 * (L ^ 2 + L + 6) ≤ (L + 1) * (L ^ 2 - L + 6) := by
  have h := remainderRatio_nonneg L hL
  nlinarith only [h]

theorem lastKernelMargin (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (ht : 0 ≤ t) (ht8 : t ≤ 8) :
    t ^ 10 / 5760 ≤ a * t ^ 9 / 720 + b * t ^ 10 / 2520 := by
  have h1 := mul_nonneg (mul_nonneg ha (pow_nonneg ht 9))
    (show 0 ≤ 8 - t by linarith)
  have h2 := mul_nonneg hb (pow_nonneg ht 10)
  have hsum := congrArg (fun z : ℝ => z * t ^ 10) hab
  nlinarith only [h1, h2, hsum]

theorem rootFactorization (rho z : ℝ) :
    z ^ 4 - ((1 - rho) * (1 + rho ^ 2)) * z -
      rho * (1 - rho + rho ^ 2) =
    (z - 1) * (z + rho) * (z ^ 2 + (1 - rho) * z + 1 - rho + rho ^ 2) := by
  ring

theorem imaginaryPartBound (rho : ℝ) :
    (2 / 3 : ℝ) ≤ (3 * rho ^ 2 - 2 * rho + 3) / 4 := by
  nlinarith [sq_nonneg (rho - 1 / 3)]

theorem negativeRootDerivativeBound (rho : ℝ) (hrho : 0 ≤ rho) :
    (3 / 4 : ℝ) ≤ 4 * rho ^ 3 + (1 - rho) * (1 + rho ^ 2) := by
  have h3 := pow_nonneg hrho 3
  nlinarith [sq_nonneg (rho - 1 / 2)]

/-- An exact lower bound on exp(8), before the analytic Taylor-series step. -/
theorem expEightTaylorBound :
    (2560 : ℚ) < ((List.range 17).map fun n =>
      (8 : ℚ) ^ n / (Nat.factorial n : ℚ)).sum := by
  norm_num [List.range_succ, Nat.factorial]

theorem exponentialQuadratic_identity (h : ℝ) :
    2560 * (1 + h + h ^ 2 / 2) - 40 * (8 + h) ^ 2 =
      1920 * h + 1240 * h ^ 2 := by
  ring

theorem exponentialQuadratic_nonneg (h : ℝ) (hh : 0 ≤ h) :
    40 * (8 + h) ^ 2 ≤ 2560 * (1 + h + h ^ 2 / 2) := by
  have h0 : 0 ≤ 1920 * h + 1240 * h ^ 2 := by positivity
  nlinarith only [h0, exponentialQuadratic_identity h]

theorem exponential_dominates_quadratic (t : ℝ) (ht : 8 ≤ t) :
    40 * t ^ 2 ≤ Real.exp t := by
  have h8 : (2560 : ℝ) < Real.exp 8 := by
    have hl : (2560 : ℝ) < ∑ n ∈ Finset.range 17,
        (8 : ℝ) ^ n / (Nat.factorial n : ℝ) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hl.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 17)
  have hh : 0 ≤ t - 8 := by linarith
  have hquad := exponentialQuadratic_nonneg (t - 8) hh
  have hTaylor := Real.quadratic_le_exp_of_nonneg hh
  have hmul : 2560 * (1 + (t - 8) + (t - 8) ^ 2 / 2) ≤
      Real.exp 8 * Real.exp (t - 8) :=
    mul_le_mul h8.le hTaylor (by positivity) (Real.exp_nonneg 8)
  rw [← Real.exp_add, show 8 + (t - 8) = t by ring] at hmul
  nlinarith only [hquad, hmul]

theorem firstTail_identity (s q : ℝ) :
    3 * (10 * s + q - 6) ^ 2 - s * (24 * (10 * s + q) + 72) =
      3 * q ^ 2 + (36 * s - 36) * q + 60 * s ^ 2 - 432 * s + 108 := by
  ring

theorem firstTail_pos (s x : ℝ) (hs : 64 ≤ s) (hx : 10 * s ≤ x) :
    0 < 3 * (x - 6) ^ 2 - s * (24 * x + 72) := by
  have hq : 0 ≤ x - 10 * s := by linarith
  have hlinear := mul_nonneg (show 0 ≤ 36 * s - 36 by linarith) hq
  have hconstant := mul_nonneg (show 0 ≤ s by linarith)
    (show 0 ≤ 60 * s - 432 by linarith)
  have heq := firstTail_identity s (x - 10 * s)
  nlinarith only [heq, hlinear, hconstant, sq_nonneg (x - 10 * s)]

theorem lastTail_identity (s q : ℝ) :
    3 * (10 * s + q - 2) ^ 2 - s * (8 * (10 * s + q) + 8) =
      3 * q ^ 2 + (52 * s - 12) * q + 220 * s ^ 2 - 128 * s + 12 := by
  ring

theorem lastTail_pos (s x : ℝ) (hs : 64 ≤ s) (hx : 10 * s ≤ x) :
    0 < 3 * (x - 2) ^ 2 - s * (8 * x + 8) := by
  have hq : 0 ≤ x - 10 * s := by linarith
  have hlinear := mul_nonneg (show 0 ≤ 52 * s - 12 by linarith) hq
  have hconstant := mul_nonneg (show 0 ≤ s by linarith)
    (show 0 ≤ 220 * s - 128 by linarith)
  have heq := lastTail_identity s (x - 10 * s)
  nlinarith only [heq, hlinear, hconstant, sq_nonneg (x - 10 * s)]

/-- Error estimate shared by the dominant Perron mode and the two real modes
of `K`. Inputs are function/derivative values at a fixed time. -/
theorem perturbedCurvature_lower (s g g1 g2 r r1 r2 E : ℝ)
    (hs : 0 ≤ s) (hE : 0 ≤ E) (hg : E ≤ g)
    (hg1 : |g1| ≤ g) (hg2 : 0 ≤ g2) (hg2g : g2 ≤ g)
    (hcurv : 0 ≤ g * g2 - g1 ^ 2)
    (hr : |r| ≤ E) (hr1 : |r1| ≤ E) (hr2 : |r2| ≤ E) :
    3 * (g - E) ^ 2 - s * (4 * E * g + 2 * E ^ 2) ≤
      s * ((g + r) * (g2 + r2) - (g1 + r1) ^ 2) + 3 * (g + r) ^ 2 := by
  have hg0 : 0 ≤ g := hE.trans hg
  have hrlo := (abs_le.mp hr).1
  have hr2lo := (abs_le.mp hr2).1
  have hgr2 := mul_le_mul_of_nonneg_left hr2lo hg0
  have hrg2 := mul_le_mul_of_nonneg_right hrlo hg2
  have hEg2 := mul_le_mul_of_nonneg_left hg2g hE
  have hg1r1 : g1 * r1 ≤ g * E := by
    have h := mul_le_mul hg1 hr1 (abs_nonneg r1) hg0
    rw [← abs_mul] at h
    exact (le_abs_self _).trans h
  have hrr2 : -(E * E) ≤ r * r2 := by
    have h := mul_le_mul hr hr2 (abs_nonneg r2) hE
    rw [← abs_mul] at h
    exact (abs_le.mp h).1
  have hr1sq : r1 ^ 2 ≤ E ^ 2 := by
    have h := mul_le_mul hr1 hr1 (abs_nonneg r1) hE
    nlinarith only [h, sq_abs r1]
  have hder : -(4 * E * g + 2 * E ^ 2) ≤
      (g + r) * (g2 + r2) - (g1 + r1) ^ 2 := by
    nlinarith only [hcurv, hgr2, hrg2, hEg2, hg1r1, hrr2, hr1sq]
  have hderS := mul_le_mul_of_nonneg_left hder hs
  have hsquare := mul_nonneg (show 0 ≤ r + E by linarith)
    (show 0 ≤ 2 * g + r - E by linarith)
  nlinarith only [hderS, hsquare]

/-- Uniform large-time curvature positivity for `J_r`, after the spectral
representation supplies a Perron mode and the three bounded error values. -/
theorem perronCurvature_pos (t x r r1 r2 : ℝ) (ht : 8 ≤ t)
    (hx : Real.exp t / 4 ≤ x)
    (hr : |r| ≤ 6) (hr1 : |r1| ≤ 6) (hr2 : |r2| ≤ 6) :
    0 < t ^ 2 * ((x + r) * (x + r2) - (x + r1) ^ 2) +
      3 * (x + r) ^ 2 := by
  have hs : 64 ≤ t ^ 2 := by nlinarith
  have hxS : 10 * t ^ 2 ≤ x := by
    have he := exponential_dominates_quadratic t ht
    linarith
  have hx0 : 0 ≤ x := by linarith
  have h := perturbedCurvature_lower (t ^ 2) x x x r r1 r2 6
    (sq_nonneg t) (by norm_num) (by linarith)
    (by simp [abs_of_nonneg hx0]) hx0 (by rfl) (by nlinarith) hr hr1 hr2
  have hp := firstTail_pos (t ^ 2) x hs hxS
  nlinarith only [h, hp]

/-- Uniform large-time curvature positivity for the last diagonal kernel,
after its nonnegative real-mode sum and the complex error bounds are supplied. -/
theorem realModesCurvature_pos (t b g g1 g2 r r1 r2 : ℝ) (ht : 8 ≤ t)
    (hb : 0 < b) (hg : b * Real.exp t / 4 ≤ g)
    (hg1 : |g1| ≤ g) (hg2 : 0 ≤ g2) (hg2g : g2 ≤ g)
    (hcurv : 0 ≤ g * g2 - g1 ^ 2)
    (hr : |r| ≤ 2 * b) (hr1 : |r1| ≤ 2 * b) (hr2 : |r2| ≤ 2 * b) :
    0 < t ^ 2 * ((g + r) * (g2 + r2) - (g1 + r1) ^ 2) +
      3 * (g + r) ^ 2 := by
  have hs : 64 ≤ t ^ 2 := by nlinarith
  have hgS : 10 * t ^ 2 * b ≤ g := by
    have he := mul_le_mul_of_nonneg_left (exponential_dominates_quadratic t ht) hb.le
    linarith
  have hgE : 2 * b ≤ g := by nlinarith
  have h := perturbedCurvature_lower (t ^ 2) g g1 g2 r r1 r2 (2 * b)
    (sq_nonneg t) (by positivity) hgE hg1 hg2 hg2g hcurv hr hr1 hr2
  have hZ : 10 * t ^ 2 ≤ g / b := (le_div_iff₀ hb).mpr hgS
  have hp := lastTail_pos (t ^ 2) (g / b) hs hZ
  have hprod := mul_pos (sq_pos_of_pos hb) hp
  have hid : b ^ 2 * (3 * (g / b - 2) ^ 2 - t ^ 2 * (8 * (g / b) + 8)) =
      3 * (g - 2 * b) ^ 2 - t ^ 2 * (8 * b * g + 8 * b ^ 2) := by
    field_simp
  rw [hid] at hprod
  nlinarith only [h, hprod]

end SSP.MixedCycle
