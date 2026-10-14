import SSPLean.K3CyclicRealTailMixed
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Scalar transition estimate for the three-state real-spectrum tail

This file isolates the sole remaining scalar inequality.  The first lemma
formalizes the weighted-degree estimate used to prove monotonicity above the
transition point.
-/

set_option autoImplicit false

namespace SSP.K3CyclicRealTail

open scoped BigOperators

/-- The unnormalized moment polynomial in the square-root variable. -/
noncomputable def rootMomentSum (n : ℕ) (b : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 2), b ^ (2 * k)

theorem rootMomentSum_nonneg {n : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ rootMomentSum n b := by
  unfold rootMomentSum
  positivity

/-- Chebyshev's sum inequality: under the decreasing weights `b^(2k)`, the
weighted average of `2k` is at most the unweighted mean `n+1`. -/
theorem rootMomentSum_weighted_degree {n : ℕ} {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    2 * (∑ k ∈ Finset.range (n + 2), (k : ℝ) * b ^ (2 * k)) ≤
      (n + 1 : ℝ) * rootMomentSum n b := by
  let s := Finset.range (n + 2)
  let f : ℕ → ℝ := fun k => k
  let g : ℕ → ℝ := fun k => b ^ (2 * k)
  have hf : MonotoneOn f s := by
    intro i hi j hj hij
    dsimp [f]
    exact_mod_cast hij
  have hg : AntitoneOn g s := by
    intro i hi j hj hij
    exact pow_le_pow_of_le_one hb0 hb1 (Nat.mul_le_mul_left 2 hij)
  have hcheb := (hf.antivaryOn hg).card_mul_sum_le_sum_mul_sum
  have hcard : s.card = n + 2 := by simp [s]
  have hsumDouble : 2 * (∑ k ∈ s, f k) =
      (n + 2 : ℝ) * (n + 1 : ℝ) := by
    dsimp [s, f]
    rw [mul_comm, ← Nat.cast_sum]
    exact_mod_cast Finset.sum_range_id_mul_two (n + 2)
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  dsimp [s, f, g] at hcheb ⊢
  rw [hcard] at hcheb
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hcheb
  unfold rootMomentSum
  have hcheb' :
      (n + 2 : ℝ) * (2 *
        (∑ k ∈ Finset.range (n + 2), (k : ℝ) * b ^ (2 * k))) ≤
        (n + 2 : ℝ) * ((n + 1 : ℝ) *
          ∑ k ∈ Finset.range (n + 2), b ^ (2 * k)) := by
    calc
      (n + 2 : ℝ) * (2 *
          (∑ k ∈ Finset.range (n + 2), (k : ℝ) * b ^ (2 * k))) =
        2 * ((n + 2 : ℝ) *
          ∑ k ∈ Finset.range (n + 2), (k : ℝ) * b ^ (2 * k)) := by ring
      _ ≤ 2 * ((∑ k ∈ Finset.range (n + 2), (k : ℝ)) *
          ∑ k ∈ Finset.range (n + 2), b ^ (2 * k)) :=
        mul_le_mul_of_nonneg_left hcheb (by norm_num)
      _ = (n + 2 : ℝ) * ((n + 1 : ℝ) *
          ∑ k ∈ Finset.range (n + 2), b ^ (2 * k)) := by
        dsimp [s, f] at hsumDouble
        rw [show 2 * ((∑ k ∈ Finset.range (n + 2), (k : ℝ)) *
            ∑ k ∈ Finset.range (n + 2), b ^ (2 * k)) =
          (2 * (∑ k ∈ Finset.range (n + 2), (k : ℝ))) *
            ∑ k ∈ Finset.range (n + 2), b ^ (2 * k) by ring,
          hsumDouble]
        ring
  have hcancel := le_of_mul_le_mul_left hcheb' hn2
  linarith

/-- The algebraic uniform moment is the preceding polynomial divided by its
number of terms. -/
theorem uniformMoment_one_sq_eq_rootMomentSum (n : ℕ) (b : ℝ) :
    uniformMoment 1 (b ^ 2) (n + 1) = rootMomentSum n b / (n + 2 : ℝ) := by
  unfold uniformMoment rootMomentSum
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hden : ((n : ℝ) + 1) + 1 = (n : ℝ) + 2 := by ring
  rw [hden]
  rw [diagonal_comm]
  unfold diagonal
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [one_pow, mul_one, ← pow_mul]

theorem hasDerivAt_rootMomentSum (n : ℕ) (b : ℝ) :
    HasDerivAt (rootMomentSum n)
      (∑ k ∈ Finset.range (n + 2), (2 * k : ℕ) * b ^ (2 * k - 1)) b := by
  unfold rootMomentSum
  apply HasDerivAt.fun_sum
  intro k hk
  simpa only [Nat.cast_mul] using hasDerivAt_pow (2 * k) b

theorem rootMomentSum_deriv_mul {n : ℕ} {b : ℝ} :
    b * deriv (rootMomentSum n) b =
      2 * ∑ k ∈ Finset.range (n + 2), (k : ℝ) * b ^ (2 * k) := by
  rw [(hasDerivAt_rootMomentSum n b).deriv, Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  cases k with
  | zero => norm_num
  | succ k =>
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, pow_succ]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- Logarithmic derivative estimate from the manuscript, without division. -/
theorem rootMomentSum_logDeriv_bound {n : ℕ} {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    b * deriv (rootMomentSum n) b ≤ (n + 1 : ℝ) * rootMomentSum n b := by
  rw [rootMomentSum_deriv_mul]
  exact rootMomentSum_weighted_degree hb0 hb1

/-- Denominator of the upper-branch transition expression. -/
noncomputable def transitionDen (n : ℕ) (b : ℝ) : ℝ :=
  b ^ (2 * n - 2) * (1 + b) ^ 2

theorem hasDerivAt_transitionDen (n : ℕ) (b : ℝ) :
    HasDerivAt (transitionDen n)
      (((2 * n - 2 : ℕ) : ℝ) * b ^ (2 * n - 2 - 1) * (1 + b) ^ 2 +
        b ^ (2 * n - 2) * (2 * (1 + b))) b := by
  unfold transitionDen
  convert! ((hasDerivAt_pow (2 * n - 2) b).mul
    (((hasDerivAt_const b (1 : ℝ)).add (hasDerivAt_id b)).pow 2)) using 1
  all_goals simp

theorem transitionDen_nonneg {n : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ transitionDen n b := by
  unfold transitionDen
  positivity

theorem transitionDen_pos {n : ℕ} {b : ℝ} (hb : 0 < b) :
    0 < transitionDen n b := by
  unfold transitionDen
  positivity

/-- The denominator has logarithmic derivative at least `n+1` once
`n ≥ 3`. -/
theorem transitionDen_logDeriv_lower {n : ℕ} (hn : 3 ≤ n) {b : ℝ}
    (hb : 0 ≤ b) :
    (n + 1 : ℝ) * transitionDen n b ≤ b * deriv (transitionDen n) b := by
  rw [(hasDerivAt_transitionDen n b).deriv]
  have hR : 1 ≤ 2 * n - 2 := by omega
  have hpow : b * b ^ (2 * n - 2 - 1) = b ^ (2 * n - 2) := by
    calc
      b * b ^ (2 * n - 2 - 1) = b ^ (2 * n - 2 - 1) * b := by ring
      _ = b ^ ((2 * n - 2 - 1) + 1) := (pow_succ b _).symm
      _ = b ^ (2 * n - 2) := by congr 1; omega
  have hdegree : (n + 1 : ℝ) ≤ (2 * n - 2 : ℕ) := by
    exact_mod_cast (show n + 1 ≤ 2 * n - 2 by omega)
  have hbase : 0 ≤ b ^ (2 * n - 2) * (1 + b) ^ 2 := by positivity
  have hmainterm :
      b * (((2 * n - 2 : ℕ) : ℝ) * b ^ (2 * n - 2 - 1) * (1 + b) ^ 2) =
        ((2 * n - 2 : ℕ) : ℝ) *
          (b ^ (2 * n - 2) * (1 + b) ^ 2) := by
    calc
      b * (((2 * n - 2 : ℕ) : ℝ) * b ^ (2 * n - 2 - 1) * (1 + b) ^ 2) =
          ((2 * n - 2 : ℕ) : ℝ) *
            (b * b ^ (2 * n - 2 - 1)) * (1 + b) ^ 2 := by ring
      _ = ((2 * n - 2 : ℕ) : ℝ) *
          (b ^ (2 * n - 2) * (1 + b) ^ 2) := by rw [hpow]; ring
  have hsecond : 0 ≤ b * (b ^ (2 * n - 2) * (2 * (1 + b))) := by positivity
  unfold transitionDen
  have hmain := mul_le_mul_of_nonneg_right hdegree hbase
  calc
    (n + 1 : ℝ) * (b ^ (2 * n - 2) * (1 + b) ^ 2) ≤
        ((2 * n - 2 : ℕ) : ℝ) *
        (b ^ (2 * n - 2) * (1 + b) ^ 2) := hmain
    _ = b * (((2 * n - 2 : ℕ) : ℝ) * b ^ (2 * n - 2 - 1) *
        (1 + b) ^ 2) := hmainterm.symm
    _ ≤ b * (((2 * n - 2 : ℕ) : ℝ) * b ^ (2 * n - 2 - 1) *
        (1 + b) ^ 2) + b * (b ^ (2 * n - 2) * (2 * (1 + b))) := le_add_of_nonneg_right hsecond
    _ = b * (((2 * n - 2 : ℕ) : ℝ) * b ^ (2 * n - 2 - 1) *
          (1 + b) ^ 2 + b ^ (2 * n - 2) * (2 * (1 + b))) := by ring

/-- Upper-branch expression, with harmless constants omitted. -/
noncomputable def highTransitionCore (n : ℕ) (b : ℝ) : ℝ :=
  rootMomentSum n b / transitionDen n b

theorem hasDerivAt_highTransitionCore {n : ℕ} {b : ℝ} (hb : 0 < b) :
    HasDerivAt (highTransitionCore n)
      ((deriv (rootMomentSum n) b * transitionDen n b -
          rootMomentSum n b * deriv (transitionDen n) b) /
        transitionDen n b ^ 2) b := by
  unfold highTransitionCore
  have hden : transitionDen n b ≠ 0 := (transitionDen_pos hb).ne'
  convert! ((hasDerivAt_rootMomentSum n b).div
    (hasDerivAt_transitionDen n b) hden) using 1
  all_goals
    rw [(hasDerivAt_rootMomentSum n b).deriv,
      (hasDerivAt_transitionDen n b).deriv]

/-- The upper-branch expression is pointwise nonincreasing on `(0,1]`. -/
theorem deriv_highTransitionCore_nonpos {n : ℕ} (hn : 3 ≤ n) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b ≤ 1) : deriv (highTransitionCore n) b ≤ 0 := by
  have hS := rootMomentSum_logDeriv_bound (n := n) hb0.le hb1
  have hD := transitionDen_logDeriv_lower hn hb0.le
  have hS0 := rootMomentSum_nonneg (n := n) hb0.le
  have hD0 := transitionDen_nonneg (n := n) hb0.le
  have hleft := mul_le_mul_of_nonneg_right hS hD0
  have hright := mul_le_mul_of_nonneg_left hD hS0
  have hcross : deriv (rootMomentSum n) b * transitionDen n b ≤
      rootMomentSum n b * deriv (transitionDen n) b := by
    apply le_of_mul_le_mul_left _ hb0
    calc
      b * (deriv (rootMomentSum n) b * transitionDen n b) =
          (b * deriv (rootMomentSum n) b) * transitionDen n b := by ring
      _ ≤ ((n + 1 : ℝ) * rootMomentSum n b) * transitionDen n b := hleft
      _ ≤ rootMomentSum n b * (b * deriv (transitionDen n) b) := by
        nlinarith
      _ = b * (rootMomentSum n b * deriv (transitionDen n) b) := by ring
  rw [(hasDerivAt_highTransitionCore hb0).deriv]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcross)
    (sq_nonneg (transitionDen n b))

theorem highTransitionCore_antitoneOn {n : ℕ} (hn : 3 ≤ n) :
    AntitoneOn (highTransitionCore n) (Set.Ioc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioc (0 : ℝ) 1)
  · intro b hb
    exact (hasDerivAt_highTransitionCore hb.1).continuousAt.continuousWithinAt
  · intro b hb
    have hbmem : b ∈ Set.Ioc (0 : ℝ) 1 := interior_subset hb
    exact (hasDerivAt_highTransitionCore hbmem.1).differentiableAt.differentiableWithinAt
  · intro b hb
    have hbmem : b ∈ Set.Ioc (0 : ℝ) 1 := interior_subset hb
    exact deriv_highTransitionCore_nonpos hn hbmem.1 hbmem.2

/-- The point where the two entries in the minimum agree. -/
noncomputable def transitionPoint (n : ℕ) : ℝ :=
  crossCoefficient n ^ (((2 * n - 2 : ℕ) : ℝ)⁻¹)

theorem crossCoefficient_pos {n : ℕ} (hn : 2 ≤ n) : 0 < crossCoefficient n := by
  unfold crossCoefficient
  apply div_pos
  · apply mul_pos (by norm_num)
    exact pow_pos (by exact_mod_cast (show 0 < n - 1 by omega)) _
  · positivity

theorem transitionPoint_pos {n : ℕ} (hn : 2 ≤ n) : 0 < transitionPoint n := by
  unfold transitionPoint
  exact Real.rpow_pos_of_pos (crossCoefficient_pos hn) _

theorem transitionPoint_pow {n : ℕ} (hn : 2 ≤ n) :
    transitionPoint n ^ (2 * n - 2) = crossCoefficient n := by
  unfold transitionPoint
  apply Real.rpow_inv_natCast_pow (crossCoefficient_nonneg n)
  omega

/-- The one numerical estimate still required at the moving transition
point.  The manuscript proves this by monotonicity in the real extension of
`n` and a check at `n = 6`. -/
def TransitionPointFactorBound (n : ℕ) : Prop :=
  12 ≤ (n + 2 : ℝ) * (1 - transitionPoint n) * (1 + transitionPoint n) ^ 3

noncomputable def transitionFactor (b : ℝ) : ℝ :=
  (1 - b) * (1 + b) ^ 3

theorem hasDerivAt_transitionFactor (b : ℝ) :
    HasDerivAt transitionFactor (2 * (1 + b) ^ 2 * (1 - 2 * b)) b := by
  unfold transitionFactor
  convert! (((hasDerivAt_const b (1 : ℝ)).sub (hasDerivAt_id b)).mul
    (((hasDerivAt_const b (1 : ℝ)).add (hasDerivAt_id b)).pow 3)) using 1
  all_goals simp; ring

theorem transitionFactor_antitoneOn :
    AntitoneOn transitionFactor (Set.Icc (1 / 2 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc (1 / 2 : ℝ) 1)
  · exact (by unfold transitionFactor; fun_prop : Continuous transitionFactor).continuousOn
  · intro b hb
    exact (hasDerivAt_transitionFactor b).differentiableAt.differentiableWithinAt
  · intro b hb
    have hbmem : b ∈ Set.Icc (1 / 2 : ℝ) 1 := interior_subset hb
    rw [(hasDerivAt_transitionFactor b).deriv]
    have hsquare : 0 ≤ (1 + b) ^ 2 := sq_nonneg _
    have hbhalf : (1 : ℝ) / 2 ≤ b := hbmem.1
    have hlinear : 1 - 2 * b ≤ 0 := by
      norm_num at hbhalf ⊢
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hsquare) hlinear

/-- The elementary geometric-series estimate at any point satisfying the
transition-factor bound. -/
theorem basicTransitionBound_of_factor {n : ℕ} {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hfactor : 12 ≤ (n + 2 : ℝ) * transitionFactor b) :
    12 * uniformMoment 1 (b ^ 2) (n + 1) / (1 + b) ^ 2 ≤ 1 := by
  have hbSq1 : b ^ 2 < 1 := by nlinarith
  have hA := uniformMoment_one_upper (m := n + 1) (sq_nonneg b) hbSq1
  have hA' : uniformMoment 1 (b ^ 2) (n + 1) ≤
      1 / ((n + 2 : ℝ) * (1 - b ^ 2)) := by
    convert hA using 1
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  have hden : 0 < (n + 2 : ℝ) * (1 - b ^ 2) := by positivity
  have hbplus : 0 < (1 + b) ^ 2 := by positivity
  have hAcentral : uniformMoment 1 (b ^ 2) (n + 1) ≤ (1 + b) ^ 2 / 12 := by
    calc
      uniformMoment 1 (b ^ 2) (n + 1) ≤
          1 / ((n + 2 : ℝ) * (1 - b ^ 2)) := hA'
      _ ≤ (1 + b) ^ 2 / 12 := by
        apply (div_le_iff₀ hden).mpr
        unfold transitionFactor at hfactor
        nlinarith
  apply (div_le_iff₀ hbplus).mpr
  nlinarith

/-- The transition-point factor estimate supplies the entire moving-tail
bound.  Below the transition point the elementary geometric-series estimate
applies; above it the normalized upper branch is antitone. -/
theorem largeTransitionTail_of_factor {n : ℕ} (hn : 6 ≤ n)
    (hfactor : TransitionPointFactorBound n) :
    LargeTransitionTail n := by
  intro b hb23 hb1
  by_cases hbEq : b = 1
  · subst b
    exact largeTransitionInequality_one hn
  have hb0 : 0 ≤ b := by linarith
  have hbLt : b < 1 := lt_of_le_of_ne hb1 hbEq
  have hp0 : 0 < transitionPoint n := transitionPoint_pos (by omega)
  have hnp2 : 0 < (n + 2 : ℝ) := by positivity
  have hpPlus : 0 < (1 + transitionPoint n) ^ 3 := by positivity
  have hpLt : transitionPoint n < 1 := by
    unfold TransitionPointFactorBound at hfactor
    by_contra h
    have : 1 ≤ transitionPoint n := le_of_not_gt h
    have hnonpos :
        (n + 2 : ℝ) * (1 - transitionPoint n) *
          (1 + transitionPoint n) ^ 3 ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hnp2.le (by linarith)) hpPlus.le
    linarith
  have hfactorP :
      12 ≤ (n + 2 : ℝ) * transitionFactor (transitionPoint n) := by
    simpa only [TransitionPointFactorBound, transitionFactor, mul_assoc] using hfactor
  by_cases hbp : b ≤ transitionPoint n
  · have hbHalf : (1 : ℝ) / 2 ≤ b := by linarith
    have hmono := transitionFactor_antitoneOn
      (show b ∈ Set.Icc (1 / 2 : ℝ) 1 from ⟨hbHalf, hb1⟩)
      (show transitionPoint n ∈ Set.Icc (1 / 2 : ℝ) 1 from
        ⟨hbHalf.trans hbp, hpLt.le⟩) hbp
    have hfactorB : 12 ≤ (n + 2 : ℝ) * transitionFactor b := by
      exact hfactorP.trans (mul_le_mul_of_nonneg_left hmono hnp2.le)
    have hbasic := basicTransitionBound_of_factor hb0 hbLt hfactorB
    have hbasic0 :
        0 ≤ 12 * uniformMoment 1 (b ^ 2) (n + 1) / (1 + b) ^ 2 := by
      exact div_nonneg
        (mul_nonneg (by norm_num)
          (uniformMoment_nonneg (by norm_num) (sq_nonneg b) _))
        (sq_nonneg _)
    unfold LargeTransitionInequality
    calc
      12 * uniformMoment 1 (b ^ 2) (n + 1) / (1 + b) ^ 2 *
          min 1 (crossCoefficient n / b ^ (2 * n - 2)) ≤
          12 * uniformMoment 1 (b ^ 2) (n + 1) / (1 + b) ^ 2 * 1 := by
            gcongr
            exact min_le_left _ _
      _ ≤ 1 := by simpa using hbasic
  · have hpb : transitionPoint n ≤ b := le_of_not_ge hbp
    have hpowB0 : 0 < b ^ (2 * n - 2) := pow_pos (by linarith) _
    have hpowP := transitionPoint_pow (n := n) (by omega)
    have hpowLe : crossCoefficient n ≤ b ^ (2 * n - 2) := by
      rw [← hpowP]
      exact pow_le_pow_left₀ hp0.le hpb _
    have hratio : crossCoefficient n / b ^ (2 * n - 2) ≤ 1 :=
      (div_le_one hpowB0).mpr hpowLe
    have hcore := highTransitionCore_antitoneOn (n := n) (by omega)
      (show transitionPoint n ∈ Set.Ioc (0 : ℝ) 1 from ⟨hp0, hpLt.le⟩)
      (show b ∈ Set.Ioc (0 : ℝ) 1 from ⟨by linarith, hb1⟩) hpb
    have hbasicP := basicTransitionBound_of_factor hp0.le hpLt hfactorP
    have hcoef0 : 0 ≤ 12 * crossCoefficient n / (n + 2 : ℝ) := by
      exact div_nonneg
        (mul_nonneg (by norm_num) (crossCoefficient_nonneg n)) hnp2.le
    unfold LargeTransitionInequality
    rw [min_eq_right hratio]
    rw [uniformMoment_one_sq_eq_rootMomentSum]
    have hrewriteB :
        12 * (rootMomentSum n b / (n + 2 : ℝ)) / (1 + b) ^ 2 *
            (crossCoefficient n / b ^ (2 * n - 2)) =
          (12 * crossCoefficient n / (n + 2 : ℝ)) *
            highTransitionCore n b := by
      unfold highTransitionCore transitionDen
      field_simp
    rw [hrewriteB]
    calc
      (12 * crossCoefficient n / (n + 2 : ℝ)) * highTransitionCore n b ≤
          (12 * crossCoefficient n / (n + 2 : ℝ)) *
            highTransitionCore n (transitionPoint n) := by gcongr
      _ = 12 * uniformMoment 1 (transitionPoint n ^ 2) (n + 1) /
          (1 + transitionPoint n) ^ 2 := by
        rw [uniformMoment_one_sq_eq_rootMomentSum]
        unfold highTransitionCore transitionDen
        rw [hpowP]
        field_simp [(crossCoefficient_pos (n := n) (by omega)).ne']
      _ ≤ 1 := hbasicP

/-- A convenient uniform lower bound for the rational power used below.
It is a direct consequence of `(1 + 1/m)^m ≤ exp 1 < 3`. -/
theorem ratioPow_lower_ninth {m : ℕ} (hm : 6 ≤ m) :
    (1 / 9 : ℝ) ≤ ((m : ℝ) / (m + 2)) ^ m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let a : ℝ := 1 + ((m : ℝ)⁻¹)
  have hbase : 1 + 2 / (m : ℝ) ≤ a ^ 2 := by
    dsimp [a]
    field_simp
    nlinarith [sq_nonneg (m : ℝ)]
  have hbase0 : 0 ≤ 1 + 2 / (m : ℝ) := by positivity
  have hpow := pow_le_pow_left₀ hbase0 hbase m
  have ha : a ^ m ≤ 3 := by
    exact (Real.one_add_inv_pow_le_exp (n := m)).trans
      Real.exp_one_lt_three.le
  have hden : (1 + 2 / (m : ℝ)) ^ m ≤ 9 := by
    calc
      (1 + 2 / (m : ℝ)) ^ m ≤ (a ^ 2) ^ m := hpow
      _ = (a ^ m) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
      _ ≤ 9 := by
        have hx := pow_le_pow_left₀ (by positivity : 0 ≤ a ^ m) ha 2
        norm_num at hx
        exact hx
  have hden0 : 0 < (1 + 2 / (m : ℝ)) ^ m := by positivity
  rw [show (m : ℝ) / (m + 2) = (1 + 2 / (m : ℝ))⁻¹ by field_simp]
  rw [inv_pow]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 9)).mpr
  have hi : (1 : ℝ) ≤ 9 / (1 + 2 / (m : ℝ)) ^ m :=
    (le_div_iff₀ hden0).mpr (by simpa using hden)
  simpa [div_eq_mul_inv, mul_comm] using hi

/-- For `n ≥ 7`, the moving transition point admits a simple rational
upper bound.  This avoids formalizing the real-variable monotonicity argument
from the manuscript. -/
theorem transitionPoint_le_ratio {n : ℕ} (hn : 7 ≤ n) :
    transitionPoint n ≤ (n - 1 : ℝ) / (n + 1 : ℝ) := by
  let q : ℝ := (n - 1 : ℝ) / (n + 1 : ℝ)
  have hn1 : 1 ≤ n := by omega
  have hq0 : 0 ≤ q := by
    dsimp [q]
    apply div_nonneg
    · norm_num
      exact_mod_cast hn1
    · positivity
  have hqpow : (1 / 9 : ℝ) ≤ q ^ (n - 1) := by
    have h := ratioPow_lower_ninth (m := n - 1) (by omega)
    have hbase :
        (((n - 1 : ℕ) : ℝ) / ((n - 1 : ℕ) + 2)) = q := by
      dsimp [q]
      rw [Nat.cast_sub hn1, Nat.cast_one]
      congr 1
      ring
    rwa [hbase] at h
  have hsmall : 4 / (n + 1 : ℝ) ^ 2 ≤ (1 / 9 : ℝ) := by
    have hn8 : (8 : ℝ) ≤ n + 1 := by
      exact_mod_cast (show 8 ≤ n + 1 by omega)
    have hden : 0 < (n + 1 : ℝ) ^ 2 := by positivity
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg ((n + 1 : ℝ) - 8)]
  have hcEq :
      crossCoefficient n = 4 / (n + 1 : ℝ) ^ 2 * q ^ (n - 1) := by
    unfold crossCoefficient
    dsimp [q]
    rw [Nat.cast_sub hn1, Nat.cast_one]
    rw [div_pow]
    rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
    field_simp
  have hc : crossCoefficient n ≤ q ^ (2 * n - 2) := by
    rw [hcEq]
    calc
      4 / (n + 1 : ℝ) ^ 2 * q ^ (n - 1) ≤
          q ^ (n - 1) * q ^ (n - 1) := by
        gcongr
        exact hsmall.trans hqpow
      _ = q ^ (2 * n - 2) := by
        rw [← pow_add]
        congr 1
        omega
  have hpPow := transitionPoint_pow (n := n) (by omega)
  apply (pow_le_pow_iff_left₀ (transitionPoint_pos (n := n) (by omega)).le
    hq0 (by omega : 2 * n - 2 ≠ 0)).mp
  rw [hpPow]
  exact hc

theorem transitionFactor_at_ratio {n : ℕ} (hn : 7 ≤ n) :
    12 ≤ (n + 2 : ℝ) *
      transitionFactor ((n - 1 : ℝ) / (n + 1 : ℝ)) := by
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hpoly :
      3 * (n + 1 : ℝ) ^ 4 ≤ 4 * (n + 2 : ℝ) * (n : ℝ) ^ 3 := by
    let x : ℝ := n - 7
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hid :
        4 * (n + 2 : ℝ) * (n : ℝ) ^ 3 - 3 * (n + 1 : ℝ) ^ 4 =
          x ^ 4 + 24 * x ^ 3 + 192 * x ^ 2 + 520 * x + 60 := by
      dsimp [x]
      ring
    rw [← sub_nonneg, hid]
    positivity
  have hden : 0 < (n + 1 : ℝ) ^ 4 := by positivity
  change 12 ≤ (n + 2 : ℝ) *
    ((1 - (n - 1 : ℝ) / (n + 1 : ℝ)) *
      (1 + (n - 1 : ℝ) / (n + 1 : ℝ)) ^ 3)
  rw [show
      (n + 2 : ℝ) * ((1 - (n - 1 : ℝ) / (n + 1 : ℝ)) *
          (1 + (n - 1 : ℝ) / (n + 1 : ℝ)) ^ 3) =
        16 * (n + 2 : ℝ) * (n : ℝ) ^ 3 / (n + 1 : ℝ) ^ 4 by
    field_simp
    ring]
  apply (le_div_iff₀ hden).mpr
  nlinarith

theorem transitionPointFactorBound_six : TransitionPointFactorBound 6 := by
  let p := transitionPoint 6
  have hp0 : 0 < p := transitionPoint_pos (by omega)
  have hpPow := transitionPoint_pow (n := 6) (by omega)
  have hpHalf : (1 / 2 : ℝ) ≤ p := by
    apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      hp0.le (by norm_num : (10 : ℕ) ≠ 0)).mp
    change (1 / 2 : ℝ) ^ 10 ≤ transitionPoint 6 ^ 10
    norm_num [hpPow, crossCoefficient]
  have hp23 : p ≤ (2 / 3 : ℝ) := by
    apply (pow_le_pow_iff_left₀ hp0.le (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num : (10 : ℕ) ≠ 0)).mp
    change transitionPoint 6 ^ 10 ≤ (2 / 3 : ℝ) ^ 10
    norm_num [hpPow, crossCoefficient]
  have hmono := transitionFactor_antitoneOn
    (show p ∈ Set.Icc (1 / 2 : ℝ) 1 from
      ⟨hpHalf, hp23.trans (by norm_num)⟩)
    (show (2 / 3 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 by norm_num) hp23
  have hbase : 12 ≤ (8 : ℝ) * transitionFactor (2 / 3) := by
    norm_num [transitionFactor]
  have hresult : 12 ≤ (8 : ℝ) * transitionFactor p :=
    hbase.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
  norm_num [TransitionPointFactorBound, transitionFactor, p, mul_assoc] at hresult ⊢
  exact hresult

/-- The numerical transition-point estimate.  The proof treats `n = 6`
exactly and uses the rational majorant `(n-1)/(n+1)` thereafter. -/
theorem transitionPointFactorBound {n : ℕ} (hn : 6 ≤ n) :
    TransitionPointFactorBound n := by
  rcases eq_or_lt_of_le hn with rfl | hn7
  · exact transitionPointFactorBound_six
  let p := transitionPoint n
  let q : ℝ := (n - 1 : ℝ) / (n + 1 : ℝ)
  have hp0 : 0 < p := transitionPoint_pos (by omega)
  have hpq : p ≤ q := transitionPoint_le_ratio hn7
  have hq0 : 0 ≤ q := hp0.le.trans hpq
  have hq1 : q ≤ 1 := by
    dsimp [q]
    have hden : 0 < (n + 1 : ℝ) := by positivity
    apply (div_le_one hden).mpr
    norm_num
    exact_mod_cast (show n ≤ n + 2 by omega)
  have hqfactor : 12 ≤ (n + 2 : ℝ) * transitionFactor q :=
    transitionFactor_at_ratio hn7
  by_cases hpHalf : (1 / 2 : ℝ) ≤ p
  · have hmono := transitionFactor_antitoneOn
      (show p ∈ Set.Icc (1 / 2 : ℝ) 1 from ⟨hpHalf, hpq.trans hq1⟩)
      (show q ∈ Set.Icc (1 / 2 : ℝ) 1 from
        ⟨hpHalf.trans hpq, hq1⟩) hpq
    have hresult := hqfactor.trans
      (mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ (n + 2 : ℝ)))
    simpa only [TransitionPointFactorBound, transitionFactor, p, mul_assoc]
      using hresult
  · have hpLe : p ≤ 1 / 2 := le_of_not_ge hpHalf
    by_cases hn10 : 10 ≤ n
    · have hfac : 1 ≤ transitionFactor p := by
        have hp2 : p ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_left₀ hp0.le hpLe 2
        have hp3 : p ^ 3 ≤ (1 / 2 : ℝ) ^ 3 :=
          pow_le_pow_left₀ hp0.le hpLe 3
        unfold transitionFactor
        nlinarith [mul_nonneg hp0.le
          (show 0 ≤ 2 - 2 * p ^ 2 - p ^ 3 by
            norm_num at hp2 hp3 ⊢
            linarith)]
      have hn12 : (12 : ℝ) ≤ n + 2 := by
        exact_mod_cast (show 12 ≤ n + 2 by omega)
      have hresult : 12 ≤ (n + 2 : ℝ) * transitionFactor p := by
        nlinarith [mul_le_mul_of_nonneg_left hfac
          (by positivity : 0 ≤ (n + 2 : ℝ))]
      simpa only [TransitionPointFactorBound, transitionFactor, p, mul_assoc]
        using hresult
    · have hpPow := transitionPoint_pow (n := n) (by omega)
      have hhalfPow :
          (1 / 2 : ℝ) ^ (2 * n - 2) ≤ crossCoefficient n := by
        interval_cases n <;> norm_num [crossCoefficient]
      have hpowcomp :
          (1 / 2 : ℝ) ^ (2 * n - 2) ≤ p ^ (2 * n - 2) := by
        change (1 / 2 : ℝ) ^ (2 * n - 2) ≤
          transitionPoint n ^ (2 * n - 2)
        rw [hpPow]
        exact hhalfPow
      have hpHalf' := (pow_le_pow_iff_left₀
        (by norm_num : (0 : ℝ) ≤ 1 / 2) hp0.le
        (by omega : 2 * n - 2 ≠ 0)).mp hpowcomp
      exact (hpHalf hpHalf').elim

theorem largeTransitionTail {n : ℕ} (hn : 6 ≤ n) :
    LargeTransitionTail n :=
  largeTransitionTail_of_factor hn (transitionPointFactorBound hn)

/-- Unconditional boundary-inclusive log-convexity of the normalized complete
polynomial throughout the large-index range. -/
theorem normalizedComplete_logConvex_large
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv1 : v ≤ 1)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) {n : ℕ} (hn : 6 ≤ n) :
    normalizedComplete u v n ^ 2 ≤
      normalizedComplete u v (n - 1) * normalizedComplete u v (n + 1) :=
  normalizedComplete_logConvex_of_transitionTail_all hu huv hv1 hroot hn
    (largeTransitionTail hn)

/-- Complete normalized log-convexity, combining the exact indices `1` through
`5` with the analytic tail. -/
theorem normalizedComplete_logConvex_all
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv1 : v ≤ 1)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    normalizedComplete u v n ^ 2 ≤
      normalizedComplete u v (n - 1) * normalizedComplete u v (n + 1) := by
  by_cases hn5 : n ≤ 5
  · exact normalizedComplete_logConvex_of_le_five hu (hu.trans huv) hroot hn hn5
  · exact normalizedComplete_logConvex_large hu huv hv1 hroot (by omega)

end SSP.K3CyclicRealTail
