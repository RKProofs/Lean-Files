import SSPLean.K3CyclicRealTailTransition
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Coefficient consequences of the three-state real-spectrum tail

This file starts the coefficient-tail step following normalized complete
log-convexity.  It isolates the general fact that, for a positive log-convex
sequence, moving two indices symmetrically away from one another increases
their product.
-/

set_option autoImplicit false

namespace SSP.K3CyclicRealTail

open scoped BigOperators

/-- Weighted Chebyshev inequality in the form used by the coefficient tail.
The weights need only be nonnegative. -/
theorem weightedChebyshev {ι : Type*} {s : Finset ι}
    (w f g : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hfg : MonovaryOn f g s) :
    (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i) ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * f i * g i) := by
  classical
  have hpair : ∀ i ∈ s, ∀ j ∈ s,
      0 ≤ w i * w j * (f i - f j) * (g i - g j) := by
    intro i hi j hj
    have hww : 0 ≤ w i * w j := mul_nonneg (hw i hi) (hw j hj)
    rcases lt_trichotomy (g i) (g j) with hg | hg | hg
    · have hf := hfg hi hj hg
      have hd : 0 ≤ (f i - f j) * (g i - g j) :=
        mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hf)
          (sub_nonpos.mpr hg.le)
      nlinarith
    · rw [hg, sub_self, mul_zero]
    · have hf := hfg hj hi hg
      exact mul_nonneg (mul_nonneg hww (sub_nonneg.mpr hf))
        (sub_nonneg.mpr hg.le)
  have hsum : 0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      w i * w j * (f i - f j) * (g i - g j) := by
    exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => hpair i hi j hj
  have hswap (F : ι → ι → ℝ) :
      (∑ i ∈ s, ∑ j ∈ s, F i j) = ∑ i ∈ s, ∑ j ∈ s, F j i := by
    rw [Finset.sum_comm]
  have hdiagSwap :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * f i * g i) =
        ∑ i ∈ s, ∑ j ∈ s, w i * w j * f j * g j := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      hswap (fun i j => w i * w j * f i * g i)
  have hcrossSwap :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * f i * g j) =
        ∑ i ∈ s, ∑ j ∈ s, w i * w j * f j * g i := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      hswap (fun i j => w i * w j * f i * g j)
  have hcrossSwap' :
      (∑ i ∈ s, ∑ j ∈ s, w i * (w j * (f i * g j))) =
        ∑ i ∈ s, ∑ j ∈ s, w i * (w j * (f j * g i)) := by
    simpa only [mul_assoc] using hcrossSwap
  have hid :
      (∑ i ∈ s, ∑ j ∈ s,
        w i * w j * (f i - f j) * (g i - g j)) =
        2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * f i * g i) -
          (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)) := by
    simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_mul]
    rw [← hdiagSwap, ← hcrossSwap]
    simp only [mul_comm, mul_left_comm]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← hcrossSwap']
    ring
  rw [hid] at hsum
  linarith

/-- Local log-convexity for a sequence indexed by the natural numbers. -/
def NatLogConvex (q : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → q n ^ 2 ≤ q (n - 1) * q (n + 1)

noncomputable def successiveRatio (q : ℕ → ℝ) (n : ℕ) : ℝ :=
  q (n + 1) / q n

/-- Positive local log-convexity is equivalent to monotonicity of successive
ratios in the direction needed for the coefficient argument. -/
theorem successiveRatio_monotone {q : ℕ → ℝ}
    (hq : ∀ n, 0 < q n) (hlc : NatLogConvex q) :
    Monotone (successiveRatio q) := by
  apply monotone_nat_of_le_succ
  intro n
  unfold successiveRatio
  apply (div_le_div_iff₀ (hq n) (hq (n + 1))).mpr
  have h := hlc (n + 1) (by omega)
  simpa only [Nat.add_sub_cancel, pow_two, mul_comm] using h

/-- Moving a pair of distinct indices one step toward their midpoint can only
decrease the product of a positive log-convex sequence. -/
theorem logConvex_product_inner_le_outer {q : ℕ → ℝ}
    (hq : ∀ n, 0 < q n) (hlc : NatLogConvex q)
    {i j : ℕ} (hij : i < j) :
    q (i + 1) * q (j - 1) ≤ q i * q j := by
  have hindex : i ≤ j - 1 := by omega
  have hratio := successiveRatio_monotone hq hlc hindex
  unfold successiveRatio at hratio
  have hj : j - 1 + 1 = j := by omega
  rw [hj] at hratio
  simpa only [mul_comm] using
    (div_le_div_iff₀ (hq i) (hq (j - 1))).mp hratio

noncomputable def symmetricProduct (q : ℕ → ℝ) (M i : ℕ) : ℝ :=
  q i * q (M - i)

theorem symmetricProduct_succ_le {q : ℕ → ℝ}
    (hq : ∀ n, 0 < q n) (hlc : NatLogConvex q)
    {M i : ℕ} (hi : 2 * i + 1 ≤ M) :
    symmetricProduct q M (i + 1) ≤ symmetricProduct q M i := by
  have hij : i < M - i := by omega
  have h := logConvex_product_inner_le_outer hq hlc hij
  unfold symmetricProduct
  have hsub : M - (i + 1) = M - i - 1 := by omega
  simpa only [hsub] using h

/-- On the left half of a fixed total degree, the symmetric product is
antitone as the split moves toward the center. -/
theorem symmetricProduct_antitoneOn_left {q : ℕ → ℝ}
    (hq : ∀ n, 0 < q n) (hlc : NatLogConvex q) (M : ℕ) :
    AntitoneOn (symmetricProduct q M) (Set.Iic (M / 2)) := by
  intro i hi j hj hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      have hjhalf : j + 1 ≤ M / 2 := hj
      have hstep : 2 * j + 1 ≤ M := by omega
      exact (symmetricProduct_succ_le hq hlc hstep).trans
        (ih ((Nat.le_succ j).trans hjhalf))

/-- The quadratic coefficient appearing in the split-variance formula. -/
noncomputable def splitKappa (N j : ℕ) : ℝ :=
  2 - (N : ℝ) / 2 + ((N : ℝ) - 2 * j) ^ 2 / 2

theorem splitKappa_succ_le_left {M i : ℕ} (hi : 2 * i + 1 ≤ M) :
    splitKappa (M + 6) (i + 4) ≤ splitKappa (M + 6) (i + 3) := by
  unfold splitKappa
  push_cast
  have hiR : (2 : ℝ) * i + 1 ≤ M := by exact_mod_cast hi
  nlinarith

theorem splitKappa_antitoneOn_left (M : ℕ) :
    AntitoneOn (fun i => splitKappa (M + 6) (i + 3))
      (Set.Iic (M / 2)) := by
  intro i hi j hj hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      have hjhalf : j + 1 ≤ M / 2 := hj
      have hstep : 2 * j + 1 ≤ M := by omega
      exact (splitKappa_succ_le_left hstep).trans
        (ih ((Nat.le_succ j).trans hjhalf))

/-- Distance from an index split to the nearer endpoint. -/
def splitEdge (M i : ℕ) : ℕ := min i (M - i)

theorem splitEdge_le_half {M i : ℕ} (hi : i ≤ M) : splitEdge M i ≤ M / 2 := by
  unfold splitEdge
  by_cases hleft : i ≤ M / 2
  · exact (min_le_left _ _).trans hleft
  · exact (min_le_right _ _).trans (by omega)

/-- Folding two antitone functions about a common midpoint makes them
monovary on the full interval. -/
theorem antitoneOn_fold_monovaryOn {f g : ℕ → ℝ} (M : ℕ)
    (hf : AntitoneOn f (Set.Iic (M / 2)))
    (hg : AntitoneOn g (Set.Iic (M / 2))) :
    MonovaryOn (fun i => f (splitEdge M i))
      (fun i => g (splitEdge M i)) (Set.Iic M) := by
  intro i hi j hj hlt
  have hei : splitEdge M i ∈ Set.Iic (M / 2) := splitEdge_le_half hi
  have hej : splitEdge M j ∈ Set.Iic (M / 2) := splitEdge_le_half hj
  by_cases hji : splitEdge M j ≤ splitEdge M i
  · exact hf hej hei hji
  · have hij : splitEdge M i ≤ splitEdge M j := le_of_not_ge hji
    have := hg hei hej hij
    linarith

theorem foldedProductKappa_monovaryOn {q : ℕ → ℝ}
    (hq : ∀ n, 0 < q n) (hlc : NatLogConvex q) (M : ℕ) :
    MonovaryOn
      (fun i => symmetricProduct q M (splitEdge M i))
      (fun i => splitKappa (M + 6) (splitEdge M i + 3))
      (Set.Iic M) := by
  exact antitoneOn_fold_monovaryOn M
    (symmetricProduct_antitoneOn_left hq hlc M)
    (splitKappa_antitoneOn_left M)

theorem symmetricProduct_splitEdge {q : ℕ → ℝ} {M i : ℕ} (hi : i ≤ M) :
    symmetricProduct q M (splitEdge M i) = symmetricProduct q M i := by
  unfold splitEdge
  by_cases hleft : i ≤ M / 2
  · rw [min_eq_left (by omega)]
  · rw [min_eq_right (by omega)]
    unfold symmetricProduct
    rw [Nat.sub_sub_self hi]
    ring

theorem splitKappa_splitEdge {M i : ℕ} (hi : i ≤ M) :
    splitKappa (M + 6) (splitEdge M i + 3) =
      splitKappa (M + 6) (i + 3) := by
  unfold splitEdge
  by_cases hleft : i ≤ M / 2
  · rw [min_eq_left (by omega)]
  · rw [min_eq_right (by omega)]
    unfold splitKappa
    push_cast
    have hcast : ((M - i : ℕ) : ℝ) = M - i := by
      rw [Nat.cast_sub hi]
    rw [hcast]
    ring

noncomputable def splitWeight (M i : ℕ) : ℝ :=
  ((Nat.choose (M + 6) (i + 3) * (i + 1) * (M - i + 1) : ℕ) : ℝ)

noncomputable def splitBaselineClosed (N : ℕ) : ℝ :=
  ((2 : ℝ) ^ N * ((N : ℝ) ^ 2 - 17 * N + 32) +
    4 * (N : ℝ) ^ 4 - 24 * (N : ℝ) ^ 3 + 68 * (N : ℝ) ^ 2 -
      48 * N - 64) / 4

/-- The binomial falling-factorial moments, obtained by differentiating
`(X + 1) ^ N` and evaluating at `X = 1`. -/
theorem binomial_descFactorial_moment (N r : ℕ) :
    (∑ j ∈ Finset.range (N + 1),
      (((Nat.choose N j : ℕ) : ℝ) * (Nat.descFactorial j r : ℝ))) =
      (Nat.descFactorial N r : ℝ) * (2 : ℝ) ^ (N - r) := by
  have hpoly :
      ((Polynomial.X : Polynomial ℝ) + 1) ^ N =
        ∑ j ∈ Finset.range (N + 1),
          Polynomial.C ((Nat.choose N j : ℕ) : ℝ) * Polynomial.X ^ j := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    simp
    ring
  have hd := congrArg (fun p : Polynomial ℝ => (Polynomial.derivative^[r]) p) hpoly
  rw [show ((Polynomial.X : Polynomial ℝ) + 1) =
      Polynomial.X + Polynomial.C 1 by simp,
    Polynomial.iterate_derivative_X_add_pow] at hd
  rw [Polynomial.iterate_derivative_sum] at hd
  simp_rw [Polynomial.iterate_derivative_C_mul,
    Polynomial.iterate_derivative_X_pow_eq_smul] at hd
  have heval := congrArg (Polynomial.evalRingHom (1 : ℝ)) hd
  simp only [map_sum, map_nsmul, map_mul] at heval
  norm_num at heval
  simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using heval.symm

/-- The first five falling-factorial basis polynomials. -/
noncomputable def fallingBasis (r : ℕ) (x : ℝ) : ℝ :=
  match r with
  | 0 => 1
  | 1 => x
  | 2 => x * (x - 1)
  | 3 => x * (x - 1) * (x - 2)
  | _ => x * (x - 1) * (x - 2) * (x - 3)

lemma cast_descFactorial_le_four (j r : ℕ) (hr : r ≤ 4) :
    ((j.descFactorial r : ℕ) : ℝ) = fallingBasis r j := by
  interval_cases r <;> simp only [Nat.descFactorial_succ, tsub_zero,
    Nat.descFactorial_zero, mul_one, Nat.cast_mul, Nat.cast_one, fallingBasis]
  · cases j <;> simp
    all_goals ring
  · rcases j with (_ | _ | j) <;> simp
    ring
  · rcases j with (_ | _ | _ | j) <;> simp
    ring

/-- The binomial summand before deleting the six endpoint indices. -/
noncomputable def fullSplitKernel (N j : ℕ) : ℝ :=
  (Nat.choose N j : ℝ) * ((j : ℝ) - 2) * ((N : ℝ) - j - 2) *
    (2 - (N : ℝ) / 2 + ((N : ℝ) - 2 * j) ^ 2 / 2)

theorem fullSplitKernel_sum (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), fullSplitKernel N j) =
      (2 : ℝ) ^ N * (-N^3 + 3*N^2 - 6*N + 8) +
      (Nat.descFactorial N 1 : ℝ) * (2 : ℝ) ^ (N-1) *
        (N^3/2 + N^2 - 11*N/2 + 4) +
      (Nat.descFactorial N 2 : ℝ) * (2 : ℝ) ^ (N-2) *
        (-5*N^2/2 + 17*N/2 - 8) +
      (Nat.descFactorial N 3 : ℝ) * (2 : ℝ) ^ (N-3) * (4*N-12) -
      2 * (Nat.descFactorial N 4 : ℝ) * (2 : ℝ) ^ (N-4) := by
  have hpoint : ∀ j : ℕ, fullSplitKernel N j =
      (Nat.choose N j : ℝ) *
        ((-N^3 + 3*N^2 - 6*N + 8) * fallingBasis 0 j +
         (N^3/2 + N^2 - 11*N/2 + 4) * fallingBasis 1 j +
         (-5*N^2/2 + 17*N/2 - 8) * fallingBasis 2 j +
         (4*N-12) * fallingBasis 3 j - 2 * fallingBasis 4 j) := by
    intro j
    unfold fullSplitKernel fallingBasis
    push_cast
    ring
  simp_rw [hpoint]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have hfactor (c : ℝ) (r : ℕ) :
      (∑ j ∈ Finset.range (N + 1),
        (Nat.choose N j : ℝ) * (c * fallingBasis r j)) =
        c * ∑ j ∈ Finset.range (N + 1),
          (Nat.choose N j : ℝ) * fallingBasis r j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfactor _ 0, hfactor _ 1, hfactor _ 2, hfactor _ 3,
    hfactor _ 4]
  have hm0 := binomial_descFactorial_moment N 0
  have hm1 := binomial_descFactorial_moment N 1
  have hm2 := binomial_descFactorial_moment N 2
  have hm3 := binomial_descFactorial_moment N 3
  have hm4 := binomial_descFactorial_moment N 4
  simp_rw [cast_descFactorial_le_four _ 0 (by omega)] at hm0
  simp_rw [cast_descFactorial_le_four _ 1 (by omega)] at hm1
  simp_rw [cast_descFactorial_le_four _ 2 (by omega)] at hm2
  simp_rw [cast_descFactorial_le_four _ 3 (by omega)] at hm3
  simp_rw [cast_descFactorial_le_four _ 4 (by omega)] at hm4
  rw [hm0, hm1, hm2, hm3, hm4]
  rw [← cast_descFactorial_le_four N 0 (by omega),
    ← cast_descFactorial_le_four N 1 (by omega),
    ← cast_descFactorial_le_four N 2 (by omega),
    ← cast_descFactorial_le_four N 3 (by omega),
    ← cast_descFactorial_le_four N 4 (by omega)]
  simp only [Nat.descFactorial_zero, Nat.sub_zero, Nat.cast_one]
  ring

theorem splitBaseline_as_full_sum (M : ℕ) :
    (∑ i ∈ Finset.range (M + 1),
      splitWeight M i * splitKappa (M + 6) (i + 3)) =
      (∑ j ∈ Finset.range (M + 7), fullSplitKernel (M + 6) j) -
        (fullSplitKernel (M + 6) 0 + fullSplitKernel (M + 6) 1 +
          fullSplitKernel (M + 6) 2 + fullSplitKernel (M + 6) (M + 4) +
          fullSplitKernel (M + 6) (M + 5) +
          fullSplitKernel (M + 6) (M + 6)) := by
  have hmid : ∀ i ∈ Finset.range (M + 1),
      splitWeight M i * splitKappa (M + 6) (i + 3) =
        fullSplitKernel (M + 6) (i + 3) := by
    intro i hi
    have hiM : i ≤ M := by simpa using Finset.mem_range.mp hi
    unfold splitWeight splitKappa fullSplitKernel
    push_cast
    rw [Nat.cast_sub hiM]
    ring_nf
  have hdecomp :
      (∑ j ∈ Finset.range (M + 7), fullSplitKernel (M + 6) j) =
        (fullSplitKernel (M + 6) 0 + fullSplitKernel (M + 6) 1 +
          fullSplitKernel (M + 6) 2) +
        (∑ i ∈ Finset.range (M + 1), fullSplitKernel (M + 6) (i + 3)) +
        (fullSplitKernel (M + 6) (M + 4) +
          fullSplitKernel (M + 6) (M + 5) +
          fullSplitKernel (M + 6) (M + 6)) := by
    rw [show M + 7 = 3 + (M + 4) by omega, Finset.sum_range_add,
      show M + 4 = (M + 1) + 3 by omega, Finset.sum_range_add]
    simp [Finset.sum_range_succ]
    ring_nf
  rw [Finset.sum_congr rfl hmid, hdecomp]
  ring_nf

theorem fullSplitKernel_sum_closed (M : ℕ) :
    (∑ j ∈ Finset.range (M + 7), fullSplitKernel (M + 6) j) =
      (2 : ℝ) ^ (M + 6) *
        (((M + 6 : ℕ) : ℝ) ^ 2 - 17 * (M + 6 : ℕ) + 32) / 4 := by
  rw [show M + 7 = (M + 6) + 1 by omega, fullSplitKernel_sum]
  norm_num [Nat.descFactorial_succ, pow_add]
  push_cast
  ring

theorem fullSplitKernel_endpoint_sum (M : ℕ) :
    fullSplitKernel (M + 6) 0 + fullSplitKernel (M + 6) 1 +
        fullSplitKernel (M + 6) 2 + fullSplitKernel (M + 6) (M + 4) +
        fullSplitKernel (M + 6) (M + 5) +
        fullSplitKernel (M + 6) (M + 6) =
      -(4 * (((M + 6 : ℕ) : ℝ) ^ 4) -
          24 * (((M + 6 : ℕ) : ℝ) ^ 3) +
          68 * (((M + 6 : ℕ) : ℝ) ^ 2) -
          48 * (M + 6 : ℕ) - 64) / 4 := by
  unfold fullSplitKernel
  simp [Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self]
  ring

/-- Exact evaluation of the purely binomial baseline sum. -/
theorem splitBaseline_formula (M : ℕ) :
    (∑ i ∈ Finset.range (M + 1),
      splitWeight M i * splitKappa (M + 6) (i + 3)) =
        splitBaselineClosed (M + 6) := by
  rw [splitBaseline_as_full_sum, fullSplitKernel_sum_closed,
    fullSplitKernel_endpoint_sum]
  unfold splitBaselineClosed
  ring

theorem splitBaselineClosed_nonneg {N : ℕ} (hN : 15 ≤ N) :
    0 ≤ splitBaselineClosed N := by
  let x : ℝ := N - 15
  have hx : 0 ≤ x := by
    have hNR : (15 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [x]
    linarith
  have hquad : 0 ≤ (N : ℝ) ^ 2 - 17 * N + 32 := by
    have hid : (N : ℝ) ^ 2 - 17 * N + 32 = x ^ 2 + 13 * x + 2 := by
      dsimp [x]
      ring
    rw [hid]
    positivity
  have hquartic : 0 ≤
      4 * (N : ℝ) ^ 4 - 24 * (N : ℝ) ^ 3 + 68 * (N : ℝ) ^ 2 -
        48 * N - 64 := by
    have hid :
        4 * (N : ℝ) ^ 4 - 24 * (N : ℝ) ^ 3 + 68 * (N : ℝ) ^ 2 -
            48 * N - 64 =
          4 * x ^ 4 + 216 * x ^ 3 + 4388 * x ^ 2 + 39792 * x + 136016 := by
      dsimp [x]
      ring
    rw [hid]
    positivity
  unfold splitBaselineClosed
  apply div_nonneg
  · nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N) hquad]
  · norm_num

theorem splitWeight_nonneg (M i : ℕ) : 0 ≤ splitWeight M i := by
  unfold splitWeight
  positivity

/-- Weighted Chebyshev comparison for the exact coefficient weights in the
real-spectrum variance tail. -/
theorem splitCoefficient_chebyshev {q : ℕ → ℝ}
    (hq : ∀ n, 0 < q n) (hlc : NatLogConvex q) (M : ℕ) :
    (∑ i ∈ Finset.range (M + 1), splitWeight M i * symmetricProduct q M i) *
        (∑ i ∈ Finset.range (M + 1), splitWeight M i *
          splitKappa (M + 6) (i + 3)) ≤
      (∑ i ∈ Finset.range (M + 1), splitWeight M i) *
        (∑ i ∈ Finset.range (M + 1), splitWeight M i *
          symmetricProduct q M i * splitKappa (M + 6) (i + 3)) := by
  let s := Finset.range (M + 1)
  let f : ℕ → ℝ := fun i => symmetricProduct q M (splitEdge M i)
  let g : ℕ → ℝ := fun i => splitKappa (M + 6) (splitEdge M i + 3)
  have hmono : MonovaryOn f g s := by
    intro i hi j hj hij
    have hi' : i < M + 1 := by simpa [s] using hi
    have hj' : j < M + 1 := by simpa [s] using hj
    apply foldedProductKappa_monovaryOn hq hlc M
    · exact (show i ≤ M by omega)
    · exact (show j ≤ M by omega)
    · exact hij
  have hcheb := weightedChebyshev (s := s) (splitWeight M) f g
    (fun i hi => splitWeight_nonneg M i) hmono
  dsimp [s, f, g] at hcheb
  have hprod : ∀ i ∈ Finset.range (M + 1),
      symmetricProduct q M (splitEdge M i) = symmetricProduct q M i := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact symmetricProduct_splitEdge (show i ≤ M by omega)
  have hkappa : ∀ i ∈ Finset.range (M + 1),
      splitKappa (M + 6) (splitEdge M i + 3) =
        splitKappa (M + 6) (i + 3) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact splitKappa_splitEdge (show i ≤ M by omega)
  have hfSum :
      (∑ i ∈ Finset.range (M + 1), splitWeight M i *
        symmetricProduct q M (splitEdge M i)) =
      ∑ i ∈ Finset.range (M + 1), splitWeight M i * symmetricProduct q M i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hprod i hi]
  have hgSum :
      (∑ i ∈ Finset.range (M + 1), splitWeight M i *
        splitKappa (M + 6) (splitEdge M i + 3)) =
      ∑ i ∈ Finset.range (M + 1), splitWeight M i *
        splitKappa (M + 6) (i + 3) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hkappa i hi]
  have hfgSum :
      (∑ i ∈ Finset.range (M + 1), splitWeight M i *
        symmetricProduct q M (splitEdge M i) *
          splitKappa (M + 6) (splitEdge M i + 3)) =
      ∑ i ∈ Finset.range (M + 1), splitWeight M i *
        symmetricProduct q M i * splitKappa (M + 6) (i + 3) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hprod i hi, hkappa i hi]
  rwa [hfSum, hgSum, hfgSum] at hcheb

theorem splitWeight_zero_pos (M : ℕ) : 0 < splitWeight M 0 := by
  unfold splitWeight
  norm_num
  exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega)) (by omega)

/-- Once the explicit baseline weighted average of `splitKappa` is
nonnegative, log-convexity forces the coefficient with the symmetric sequence
multiplier to be nonnegative as well. -/
theorem splitCoefficient_nonneg_of_baseline {q : ℕ → ℝ}
    (hq : ∀ n, 0 < q n) (hlc : NatLogConvex q) (M : ℕ)
    (hbase : 0 ≤ ∑ i ∈ Finset.range (M + 1),
      splitWeight M i * splitKappa (M + 6) (i + 3)) :
    0 ≤ ∑ i ∈ Finset.range (M + 1), splitWeight M i *
      symmetricProduct q M i * splitKappa (M + 6) (i + 3) := by
  have hcheb := splitCoefficient_chebyshev hq hlc M
  have hmult : 0 ≤ ∑ i ∈ Finset.range (M + 1),
      splitWeight M i * symmetricProduct q M i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (splitWeight_nonneg M i)
      (mul_nonneg (hq i).le (hq (M - i)).le)
  have hleft : 0 ≤
      (∑ i ∈ Finset.range (M + 1),
        splitWeight M i * symmetricProduct q M i) *
      (∑ i ∈ Finset.range (M + 1),
        splitWeight M i * splitKappa (M + 6) (i + 3)) :=
    mul_nonneg hmult hbase
  have hweighted : 0 ≤
      (∑ i ∈ Finset.range (M + 1), splitWeight M i) *
      (∑ i ∈ Finset.range (M + 1), splitWeight M i *
        symmetricProduct q M i * splitKappa (M + 6) (i + 3)) :=
    hleft.trans hcheb
  have hweightPos : 0 < ∑ i ∈ Finset.range (M + 1), splitWeight M i := by
    apply Finset.sum_pos'
    · intro i hi
      exact splitWeight_nonneg M i
    · refine ⟨0, by simp, splitWeight_zero_pos M⟩
  exact (mul_nonneg_iff_of_pos_left hweightPos).mp hweighted

theorem diagonal_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℕ) :
    0 ≤ diagonal u v n := by
  unfold diagonal
  positivity

theorem complete3_pos {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℕ) :
    0 < complete3 u v n := by
  induction n with
  | zero => simp [complete3]
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by rfl, complete3_succ]
      exact add_pos_of_pos_of_nonneg ih (diagonal_nonneg hu hv (n + 1))

theorem normalizedComplete_pos {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (n : ℕ) : 0 < normalizedComplete u v n := by
  unfold normalizedComplete
  exact div_pos (complete3_pos hu hv n) (by positivity)

/-- The completed normalized theorem, packaged as local sequence
log-convexity. -/
theorem normalizedComplete_natLogConvex
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv1 : v ≤ 1)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) :
    NatLogConvex (normalizedComplete u v) := by
  intro n hn
  exact normalizedComplete_logConvex_all hu huv hv1 hroot hn

/-- Symmetric products of the normalized complete sequence increase as their
indices move apart.  This is the monotonic multiplier needed in the
coefficient-tail Chebyshev argument. -/
theorem normalizedComplete_product_inner_le_outer
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv1 : v ≤ 1)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1)
    {i j : ℕ} (hij : i < j) :
    normalizedComplete u v (i + 1) * normalizedComplete u v (j - 1) ≤
      normalizedComplete u v i * normalizedComplete u v j := by
  exact logConvex_product_inner_le_outer
    (fun n => normalizedComplete_pos hu (hu.trans huv) n)
    (normalizedComplete_natLogConvex hu huv hv1 hroot) hij

/-- The far-tail coefficient is nonnegative as soon as the purely binomial
baseline sum is.  All dependence on `u` and `v` has now been discharged by
the normalized log-convexity theorem. -/
theorem normalizedComplete_splitCoefficient_nonneg_of_baseline
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv1 : v ≤ 1)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) (M : ℕ)
    (hbase : 0 ≤ ∑ i ∈ Finset.range (M + 1),
      splitWeight M i * splitKappa (M + 6) (i + 3)) :
    0 ≤ ∑ i ∈ Finset.range (M + 1), splitWeight M i *
      symmetricProduct (normalizedComplete u v) M i *
        splitKappa (M + 6) (i + 3) := by
  exact splitCoefficient_nonneg_of_baseline
    (fun n => normalizedComplete_pos hu (hu.trans huv) n)
    (normalizedComplete_natLogConvex hu huv hv1 hroot) M hbase

/-- Far-tail coefficient nonnegativity with the binomial baseline evaluated
explicitly. -/
theorem normalizedComplete_splitCoefficient_nonneg_of_baseline_formula
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv1 : v ≤ 1)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) {M : ℕ} (hM : 9 ≤ M) :
    0 ≤ ∑ i ∈ Finset.range (M + 1), splitWeight M i *
      symmetricProduct (normalizedComplete u v) M i *
        splitKappa (M + 6) (i + 3) := by
  apply normalizedComplete_splitCoefficient_nonneg_of_baseline hu huv hv1 hroot
  rw [splitBaseline_formula]
  exact splitBaselineClosed_nonneg (by omega)

end SSP.K3CyclicRealTail
