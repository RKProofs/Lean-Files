import Mathlib.Algebra.BigOperators.Fin
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

/-!
# The chain inequality `3(n+1) h₁h₃ ≥ 2(n+2) h₂²`

This file proves the case `k = 2` of the moment hierarchy conjecture for hypoexponential
(deterministic-chain) absorption times, in every order `n`.

For nonnegative `t₁, …, tₙ` let `pᵣ = ∑ᵢ tᵢʳ` be the power sums and `hₖ` the complete
homogeneous symmetric polynomials.  Newton's identities give
`h₁ = p₁`, `h₂ = (p₁² + p₂)/2`, `h₃ = (p₁³ + 3p₁p₂ + 2p₃)/6`, and substituting them turns the
target into a polynomial in the power sums alone which factors as

  `3(n+1) h₁h₃ − 2(n+2) h₂² = (n+1)(p₁p₃ − p₂²) + ½(p₁² + p₂)(n·p₂ − p₁²)`.

Both brackets are nonnegative by Cauchy–Schwarz, with Lagrange forms
`n·p₂ − p₁² = ∑_{i<j} (tᵢ − tⱼ)²` and `p₁p₃ − p₂² = ∑_{i<j} tᵢtⱼ(tᵢ − tⱼ)²`.

## Main results

* `hgen_identity` — the power-sum identity, over an arbitrary commutative ring.
* `chain_ineq` — the inequality itself, for nonnegative `t`.
* `chain_ineq_h` — the same, stated via `h₁, h₂, h₃`.
-/

namespace SSP.Chain

open Finset

variable {ι : Type*}

/-- The `r`-th power sum of `t` over `s`. -/
def psum (s : Finset ι) (t : ι → ℝ) (r : ℕ) : ℝ := ∑ i ∈ s, (t i) ^ r

/-- **The algebraic core.**  The combination `3(n+1)h₁h₃ − 2(n+2)h₂²`, once written in power
sums via Newton's identities, splits into the two Cauchy–Schwarz brackets.  This is a ring
identity in `n, p₁, p₂, p₃`, so it holds for every `n` at once. -/
theorem hgen_identity (n p₁ p₂ p₃ : ℝ) :
    3 * (n + 1) * p₁ * ((p₁ ^ 3 + 3 * p₁ * p₂ + 2 * p₃) / 6)
        - 2 * (n + 2) * ((p₁ ^ 2 + p₂) / 2) ^ 2
      = (n + 1) * (p₁ * p₃ - p₂ ^ 2) + (p₁ ^ 2 + p₂) * (n * p₂ - p₁ ^ 2) / 2 := by
  ring

/-- **Lagrange's identity**: `n·p₂ − p₁² = ∑_{i<j} (tᵢ − tⱼ)²`, here in the symmetric form
`n·p₂ − p₁² = ½ ∑ᵢ∑ⱼ (tᵢ − tⱼ)²`. -/
theorem lagrange_one (s : Finset ι) (t : ι → ℝ) :
    (s.card : ℝ) * psum s t 2 - (psum s t 1) ^ 2
      = (∑ i ∈ s, ∑ j ∈ s, (t i - t j) ^ 2) / 2 := by
  have key : ∑ i ∈ s, ∑ j ∈ s, (t i - t j) ^ 2
      = 2 * ((s.card : ℝ) * (∑ j ∈ s, (t j) ^ 2) - (∑ j ∈ s, t j) ^ 2) := by
    have expand : ∀ i ∈ s, ∑ j ∈ s, (t i - t j) ^ 2
        = (s.card : ℝ) * (t i) ^ 2 - 2 * (t i) * (∑ j ∈ s, t j) + ∑ j ∈ s, (t j) ^ 2 := by
      intro i _
      have e2 : ∀ j ∈ s, (t i - t j) ^ 2
          = (t i) ^ 2 - 2 * (t i) * t j + (t j) ^ 2 := fun j _ => by ring
      rw [Finset.sum_congr rfl e2, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, ← Finset.mul_sum]
      simp [nsmul_eq_mul]
    rw [Finset.sum_congr rfl expand]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      ← Finset.mul_sum, ← Finset.sum_mul, nsmul_eq_mul]
    ring
  rw [key]
  simp only [psum, pow_one]
  ring

/-- **Weighted Lagrange identity**: `p₁p₃ − p₂² = ∑_{i<j} tᵢtⱼ(tᵢ − tⱼ)²`, in the symmetric
form `p₁p₃ − p₂² = ½ ∑ᵢ∑ⱼ tᵢtⱼ(tᵢ − tⱼ)²`. -/
theorem lagrange_two (s : Finset ι) (t : ι → ℝ) :
    psum s t 1 * psum s t 3 - (psum s t 2) ^ 2
      = (∑ i ∈ s, ∑ j ∈ s, t i * t j * (t i - t j) ^ 2) / 2 := by
  have key : ∑ i ∈ s, ∑ j ∈ s, t i * t j * (t i - t j) ^ 2
      = 2 * ((∑ j ∈ s, t j) * (∑ j ∈ s, (t j) ^ 3) - (∑ j ∈ s, (t j) ^ 2) ^ 2) := by
    have expand : ∀ i ∈ s, ∑ j ∈ s, t i * t j * (t i - t j) ^ 2
        = (t i) ^ 3 * (∑ j ∈ s, t j) - 2 * (t i) ^ 2 * (∑ j ∈ s, (t j) ^ 2)
          + (t i) * (∑ j ∈ s, (t j) ^ 3) := by
      intro i _
      have e2 : ∀ j ∈ s, t i * t j * (t i - t j) ^ 2
          = (t i) ^ 3 * t j - 2 * (t i) ^ 2 * (t j) ^ 2
            + (t i) * (t j) ^ 3 := fun j _ => by ring
      rw [Finset.sum_congr rfl e2, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl expand]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [key]
  simp only [psum, pow_one]
  ring

/-- `n·p₂ − p₁² ≥ 0` (Cauchy–Schwarz). -/
theorem cs_one (s : Finset ι) (t : ι → ℝ) :
    0 ≤ (s.card : ℝ) * psum s t 2 - (psum s t 1) ^ 2 := by
  rw [lagrange_one]
  positivity

/-- `p₁p₃ − p₂² ≥ 0` for nonnegative `t` (Cauchy–Schwarz on `t^{1/2}·t^{3/2}`). -/
theorem cs_two (s : Finset ι) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i) :
    0 ≤ psum s t 1 * psum s t 3 - (psum s t 2) ^ 2 := by
  rw [lagrange_two]
  have : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, t i * t j * (t i - t j) ^ 2 :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
      mul_nonneg (mul_nonneg (ht i hi) (ht j hj)) (sq_nonneg _)
  linarith

/-- **The chain inequality, in power-sum form.**  For nonnegative `t` indexed by a finset of
cardinality `n`,
`3(n+1)h₁h₃ − 2(n+2)h₂² = (n+1)(p₁p₃ − p₂²) + ½(p₁²+p₂)(n·p₂ − p₁²) ≥ 0`. -/
theorem chain_ineq (s : Finset ι) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i) :
    0 ≤ 3 * ((s.card : ℝ) + 1) * psum s t 1
          * ((psum s t 1 ^ 3 + 3 * psum s t 1 * psum s t 2 + 2 * psum s t 3) / 6)
        - 2 * ((s.card : ℝ) + 2) * ((psum s t 1 ^ 2 + psum s t 2) / 2) ^ 2 := by
  rw [hgen_identity]
  have h1 := cs_one s t
  have h2 := cs_two s t ht
  have hp₁ : 0 ≤ psum s t 1 := Finset.sum_nonneg fun i hi => by simpa using ht i hi
  have hp₂ : 0 ≤ psum s t 2 := Finset.sum_nonneg fun i hi => by positivity
  have hcard : (0:ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have t1 : 0 ≤ ((s.card : ℝ) + 1) * (psum s t 1 * psum s t 3 - psum s t 2 ^ 2) :=
    mul_nonneg (by linarith) h2
  have t2 : 0 ≤ (psum s t 1 ^ 2 + psum s t 2)
      * ((s.card : ℝ) * psum s t 2 - psum s t 1 ^ 2) / 2 := by
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (by positivity) h1
  linarith

/-! ## The upper bound `h₁h₃ ≤ h₂²`

The spectral chain ratio is confined to `[2(n+2)/(3(n+1)), 1]`.  The upper end is the `k = 2`
log-concavity of the complete homogeneous symmetric polynomials.  In power sums it reads
`12(h₂² − h₁h₃) = p₁⁴ − 4p₁p₃ + 3p₂²`, and the inequality follows from the elementary bounds
`p₃ ≤ M·p₂` and `M² ≤ p₂ ≤ M·p₁`, where `M = maxᵢ tᵢ`. -/

/-- The power-sum identity behind `h₁h₃ ≤ h₂²`: a ring identity, valid for every `n`. -/
theorem hupper_identity (p₁ p₂ p₃ : ℝ) :
    ((p₁ ^ 2 + p₂) / 2) ^ 2 - p₁ * ((p₁ ^ 3 + 3 * p₁ * p₂ + 2 * p₃) / 6)
      = (p₁ ^ 4 - 4 * p₁ * p₃ + 3 * p₂ ^ 2) / 12 := by
  ring

/-- `p₃ ≤ M · p₂` when every `tᵢ ≤ M`. -/
theorem psum3_le (s : Finset ι) (t : ι → ℝ) (M : ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) (hM : ∀ i ∈ s, t i ≤ M) :
    psum s t 3 ≤ M * psum s t 2 := by
  simp only [psum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h0 := ht i hi
  nlinarith [sq_nonneg (t i), hM i hi]

/-- `p₂ ≤ M · p₁` when every `tᵢ ≤ M`. -/
theorem psum2_le (s : Finset ι) (t : ι → ℝ) (M : ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) (hM : ∀ i ∈ s, t i ≤ M) :
    psum s t 2 ≤ M * psum s t 1 := by
  simp only [psum, Finset.mul_sum, pow_one]
  refine Finset.sum_le_sum fun i hi => ?_
  have h0 := ht i hi
  nlinarith [hM i hi]

/-- **The arithmetic core of the upper bound.**  Given `0 ≤ M ≤ p₁`, `M² ≤ p₂ ≤ M·p₁` and
`p₃ ≤ M·p₂`, we get `p₁⁴ + 3p₂² ≥ 4p₁p₃`.  Normalising `p₁ = 1`, the function
`q ↦ 1 + 3q² − 4Mq` is convex with vertex `2M/3`; on `M ≤ 2/3` the vertex value is
`1 − 4M²/3 ≥ 0`, and otherwise the minimum sits at `q = M²`, where the value factors as
`(M−1)²(3M²+2M+1) ≥ 0`. -/
theorem hupper_arith (p₁ p₂ p₃ M : ℝ)
    (hp₁ : 0 < p₁) (h2lo : M ^ 2 ≤ p₂) (h2hi : p₂ ≤ M * p₁) (h3 : p₃ ≤ M * p₂) :
    0 ≤ p₁ ^ 4 - 4 * p₁ * p₃ + 3 * p₂ ^ 2 := by
  have key : 0 ≤ p₁ ^ 4 - 4 * p₁ * (M * p₂) + 3 * p₂ ^ 2 := by
    nlinarith [sq_nonneg (3 * p₂ - 2 * M * p₁), sq_nonneg (M - p₁), sq_nonneg M,
      sq_nonneg (M * p₁ - p₂), mul_pos hp₁ hp₁, sq_nonneg (p₁ - M)]
  nlinarith [mul_le_mul_of_nonneg_left h3 (le_of_lt hp₁)]

/-- **`h₁h₃ ≤ h₂²` for nonnegative `t`** — the upper end of the window `[2(n+2)/(3(n+1)), 1]`.
Stated in power sums, with `M` any upper bound for the `tᵢ` satisfying `M² ≤ p₂`
(e.g. `M = maxᵢ tᵢ`, attained at some index, so that `M² ≤ ∑ tᵢ² = p₂`). -/
theorem hupper (s : Finset ι) (t : ι → ℝ) (M : ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) (hM : ∀ i ∈ s, t i ≤ M)
    (hp₁ : 0 < psum s t 1) (h2lo : M ^ 2 ≤ psum s t 2) :
    psum s t 1 * ((psum s t 1 ^ 3 + 3 * psum s t 1 * psum s t 2 + 2 * psum s t 3) / 6)
      ≤ ((psum s t 1 ^ 2 + psum s t 2) / 2) ^ 2 := by
  have hp₂ : 0 ≤ psum s t 2 := Finset.sum_nonneg fun i hi => by positivity
  have := hupper_arith (psum s t 1) (psum s t 2) (psum s t 3) M hp₁ h2lo
    (psum2_le s t M ht hM) (psum3_le s t M ht hM)
  have hid := hupper_identity (psum s t 1) (psum s t 2) (psum s t 3)
  linarith

/-- **The chain inequality in `h`-form.**  Supplying `h₁, h₂, h₃` through Newton's identities,
the conclusion reads `2(n+2)h₂² ≤ 3(n+1)h₁h₃`, which is the case `k = 2` of the moment
hierarchy for a hypoexponential of length `n = #s`.  Equality holds exactly when all `tᵢ`
agree (`Erlang(n)`), so the constant `2(n+2)/(3(n+1))` is sharp. -/
theorem chain_ineq_h (s : Finset ι) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i)
    (h₁ h₂ h₃ : ℝ)
    (e₁ : h₁ = psum s t 1)
    (e₂ : h₂ = (psum s t 1 ^ 2 + psum s t 2) / 2)
    (e₃ : h₃ = (psum s t 1 ^ 3 + 3 * psum s t 1 * psum s t 2 + 2 * psum s t 3) / 6) :
    2 * ((s.card : ℝ) + 2) * h₂ ^ 2 ≤ 3 * ((s.card : ℝ) + 1) * h₁ * h₃ := by
  have := chain_ineq s t ht
  rw [e₁, e₂, e₃]
  linarith

/-! ## The signed-weight dichotomy

Writing `aₖ = ∑ⱼ cⱼ tⱼᵏ` in the eigenbasis of `−T` (real positive spectrum, diagonalisable),
with `∑ⱼ cⱼ = 1`, the case `c ≥ 0` — a genuine mixture of exponentials — is immediate from
Cauchy–Schwarz, leaving only signed weights. -/

/-- Weighted moments of a nonnegative weight `c` against nonnegative `t`. -/
def wmom (s : Finset ι) (c t : ι → ℝ) (k : ℕ) : ℝ := ∑ i ∈ s, c i * (t i) ^ k

/-- **The nonnegative-weight case.**  If `c ≥ 0` and `t ≥ 0` then `a₂² ≤ a₁a₃`, so the ratio
`a₁a₃/a₂²` is at least `1` and the `k = 2` hierarchy bound holds with room to spare.

This is Cauchy–Schwarz for the weight `c` applied to `t^{1/2}` and `t^{3/2}`: with
`u i = √(c i · t i)` and `v i = √(c i · t i³)` one has `∑ uᵢvᵢ = a₂`, `∑ uᵢ² = a₁`,
`∑ vᵢ² = a₃`. -/
theorem wmom_cauchy_schwarz (s : Finset ι) (c t : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (ht : ∀ i ∈ s, 0 ≤ t i) :
    (wmom s c t 2) ^ 2 ≤ wmom s c t 1 * wmom s c t 3 := by
  classical
  set u : ι → ℝ := fun i => Real.sqrt (c i * t i) with hu
  set v : ι → ℝ := fun i => Real.sqrt (c i * (t i) ^ 3) with hv
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s u v
  -- identify the three sums
  have e1 : ∑ i ∈ s, u i * v i = wmom s c t 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have h0 : 0 ≤ c i * t i := mul_nonneg (hc i hi) (ht i hi)
    have hti := ht i hi
    have h1 : 0 ≤ c i * (t i) ^ 3 := mul_nonneg (hc i hi) (by positivity)
    change Real.sqrt (c i * t i) * Real.sqrt (c i * (t i) ^ 3) = c i * (t i) ^ 2
    rw [← Real.sqrt_mul h0]
    have hsq : c i * t i * (c i * (t i) ^ 3) = (c i * (t i) ^ 2) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq (mul_nonneg (hc i hi) (by positivity))]
  have e2 : ∑ i ∈ s, (u i) ^ 2 = wmom s c t 1 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    change Real.sqrt (c i * t i) ^ 2 = c i * (t i) ^ 1
    rw [Real.sq_sqrt (mul_nonneg (hc i hi) (ht i hi))]; ring
  have e3 : ∑ i ∈ s, (v i) ^ 2 = wmom s c t 3 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hti := ht i hi
    change Real.sqrt (c i * (t i) ^ 3) ^ 2 = c i * (t i) ^ 3
    rw [Real.sq_sqrt (mul_nonneg (hc i hi) (by positivity))]
  rw [e1, e2, e3] at hcs
  exact hcs

/-- **The `k = 2` hierarchy bound for nonnegative spectral weights.**  With `κ ≤ 1` — in
particular `κ = 2(n+2)/(3(n+1))`, which is at most `1` — the bound follows at once. -/
theorem hierarchy_of_nonneg_weights (s : Finset ι) (c t : ι → ℝ) (κ : ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (ht : ∀ i ∈ s, 0 ≤ t i) (hκ : κ ≤ 1) :
    κ * (wmom s c t 2) ^ 2 ≤ wmom s c t 1 * wmom s c t 3 := by
  have hcs := wmom_cauchy_schwarz s c t hc ht
  nlinarith [sq_nonneg (wmom s c t 2)]

/-! ## The Coxian case at order two

A Coxian law of order `2` has holding means `t₁, t₂ > 0` and continuation probability
`p ∈ [0,1]`, with `a₁ = t₁ + p t₂`, `a₂ = t₁² + p t₁t₂ + p t₂²`,
`a₃ = t₁³ + p t₁²t₂ + p t₁t₂² + p t₂³`.  The bound `a₁a₃/a₂² ≥ 8/9` holds, and the proof is the
endpoint/vertex dichotomy for a quadratic in `p`. -/

/-- The `E`-polynomial of the order-two Coxian law, `E = 9a₁a₃ − 8a₂²`. -/
noncomputable def coxE (t₁ t₂ p : ℝ) : ℝ :=
  9 * (t₁ + p * t₂) * (t₁^3 + p * t₁^2 * t₂ + p * t₁ * t₂^2 + p * t₂^3)
    - 8 * (t₁^2 + p * t₁ * t₂ + p * t₂^2)^2

/-- `E` in the collected form used in the proof: a quadratic in `p`. -/
theorem coxE_quadratic (t₁ t₂ p : ℝ) :
    coxE t₁ t₂ p
      = p^2 * t₂^2 * (t₁^2 - 7*t₁*t₂ + t₂^2)
        + p * t₁ * t₂ * (9*t₂^2 - 7*t₁*t₂ + 2*t₁^2)
        + t₁^4 := by
  unfold coxE; ring

/-- At `p = 1` the Coxian law is the pure two-chain, and `E` factors. -/
theorem coxE_one (t₁ t₂ : ℝ) :
    coxE t₁ t₂ 1 = (t₁ - t₂)^2 * (t₁^2 + 4*t₁*t₂ + t₂^2) := by
  unfold coxE; ring

/-- At `p = 0` only the first state is visited, and `E = t₁⁴`. -/
theorem coxE_zero (t₁ t₂ : ℝ) : coxE t₁ t₂ 0 = t₁^4 := by
  unfold coxE; ring

/-- **`E ≥ 0` for the order-two Coxian law.**  Equivalently `a₁a₃ ≥ (8/9) a₂²`.

The proof is by the endpoint/vertex dichotomy on the quadratic in `p`, split on the sign of
`q = t₁² − 7t₁t₂ + t₂²`: when `q < 0` the parabola opens downward so the minimum over `[0,1]`
sits at an endpoint (both nonnegative), and when `q ≥ 0` the critical point is negative so `E` is
increasing on `[0,1]` with minimum `E(0) = t₁⁴`. -/
theorem coxE_nonneg (t₁ t₂ p : ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ coxE t₁ t₂ p := by
  rw [coxE_quadratic]
  rcases le_or_gt 0 (t₁^2 - 7*t₁*t₂ + t₂^2) with hq | hq
  · -- upward (or degenerate): the linear coefficient is positive, so all terms are ≥ 0
    have hlin : 0 < 9*t₂^2 - 7*t₁*t₂ + 2*t₁^2 := by
      nlinarith [sq_nonneg (3*t₂ - t₁), sq_nonneg t₁, sq_nonneg t₂]
    have h1 : 0 ≤ p^2 * t₂^2 * (t₁^2 - 7*t₁*t₂ + t₂^2) := by positivity
    have h2 : 0 ≤ p * t₁ * t₂ * (9*t₂^2 - 7*t₁*t₂ + 2*t₁^2) :=
      mul_nonneg (by positivity) (le_of_lt hlin)
    have h3 : 0 ≤ t₁^4 := by positivity
    linarith
  · -- downward: minimum over [0,1] is at an endpoint; interpolate
    have hE0 : coxE t₁ t₂ 0 = t₁^4 := coxE_zero t₁ t₂
    have hE1 : coxE t₁ t₂ 1 = (t₁ - t₂)^2 * (t₁^2 + 4*t₁*t₂ + t₂^2) := coxE_one t₁ t₂
    have h0 : 0 ≤ t₁^4 := by positivity
    have h1 : 0 ≤ (t₁ - t₂)^2 * (t₁^2 + 4*t₁*t₂ + t₂^2) := by positivity
    -- concavity in p: E(p) ≥ (1-p)·E(0) + p·E(1) when the leading coefficient is ≤ 0
    have key : p^2 * t₂^2 * (t₁^2 - 7*t₁*t₂ + t₂^2)
          + p * t₁ * t₂ * (9*t₂^2 - 7*t₁*t₂ + 2*t₁^2)
          + t₁^4
        - ((1-p) * t₁^4 + p * ((t₁ - t₂)^2 * (t₁^2 + 4*t₁*t₂ + t₂^2)))
        = (p - p^2) * (-(t₂^2 * (t₁^2 - 7*t₁*t₂ + t₂^2))) := by ring
    have hpp : 0 ≤ p - p^2 := by nlinarith
    have hneg : 0 ≤ -(t₂^2 * (t₁^2 - 7*t₁*t₂ + t₂^2)) := by
      have : 0 < t₂^2 := by positivity
      nlinarith
    nlinarith [mul_nonneg hpp hneg, h0, h1, hp0, hp1]

/-- **The order-two Coxian bound in ratio form**: `a₁a₃ ≥ (8/9)·a₂²`, i.e.
`8a₂² ≤ 9a₁a₃`, for every `t₁, t₂ > 0` and `p ∈ [0,1]`.  Equality holds exactly at `p = 1`,
`t₁ = t₂`, which is `Erlang(2)`. -/
theorem coxian_ratio_two (t₁ t₂ p : ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    8 * (t₁^2 + p*t₁*t₂ + p*t₂^2)^2
      ≤ 9 * (t₁ + p*t₂) * (t₁^3 + p*t₁^2*t₂ + p*t₁*t₂^2 + p*t₂^3) := by
  have h := coxE_nonneg t₁ t₂ p ht₁ ht₂ hp0 hp1
  unfold coxE at h
  linarith

/-! ## Order three: the `p₂`-dichotomy

For the order-three Coxian law, `E = 12a₁a₃ − 10a₂²` is quadratic in `p₂` with leading
coefficient `2p₁²t₃²Q`, `Q = e₁² − 6e₂`.  Two facts make the dichotomy work, and both are
recorded here: the `p₂ = 0` endpoint reduces to the order-two bound plus a square, and `Q ≥ 0`
forces the domination `t₁ ≥ 2(t₂+t₃)` which pushes the critical point out of `[0,1]`. -/

/-- **The `p₂ = 0` endpoint.**  Truncating the chain keeps the order-three constant, and
`12a₁a₃ − 10a₂² = (4/3)(9a₁a₃ − 8a₂²) + (2/3)a₂²`, so it is nonnegative by `coxE_nonneg`. -/
theorem coxE3_endpoint_zero (t₁ t₂ p : ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ 12 * (t₁ + p*t₂) * (t₁^3 + p*t₁^2*t₂ + p*t₁*t₂^2 + p*t₂^3)
          - 10 * (t₁^2 + p*t₁*t₂ + p*t₂^2)^2 := by
  have h := coxE_nonneg t₁ t₂ p ht₁ ht₂ hp0 hp1
  unfold coxE at h
  have hsq : (0:ℝ) ≤ (t₁^2 + p*t₁*t₂ + p*t₂^2)^2 := sq_nonneg _
  -- 12a₁a₃ − 10a₂² = (4/3)·coxE + (2/3)·a₂²
  nlinarith [h, hsq]

/-- **`Q ≥ 0` forces domination.**  If `t₁` is the largest and
`Q = t₁²+t₂²+t₃² − 4(t₁t₂+t₁t₃+t₂t₃) ≥ 0`, then `t₁ ≥ 2(t₂+t₃)`.

The reason: writing `t₁ = t₂+t₃+d`, `Q = d² − 2d(t₂+t₃) − 2t₂² − 10t₂t₃ − 2t₃²`, whose value at
`d = t₂+t₃` is `−3(t₂²+4t₂t₃+t₃²) < 0`; as `Q` is increasing in `d` past its vertex,
nonnegativity forces `d ≥ t₂+t₃`. -/
theorem Q_nonneg_domination (t₁ t₂ t₃ : ℝ) (ht₂ : 0 ≤ t₂) (ht₃ : 0 ≤ t₃)
    (hmax₂ : t₂ ≤ t₁) (hmax₃ : t₃ ≤ t₁)
    (hQ : 0 ≤ t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 - 4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃)) :
    2*(t₂ + t₃) ≤ t₁ := by
  by_contra h
  push Not at h
  -- on `t₁ < 2(t₂+t₃)` together with `t₂,t₃ ≤ t₁`, the form `Q` is strictly negative
  nlinarith [sq_nonneg (t₁ - t₂ - t₃), sq_nonneg (t₂ - t₃), mul_nonneg ht₂ ht₃,
    sq_nonneg (t₁ - t₂), sq_nonneg (t₁ - t₃), mul_nonneg ht₂ ht₂, mul_nonneg ht₃ ht₃]

/-- **`G₀ > 0` unconditionally.**  `G₀/t₁` is a quadratic in `t₁` with negative discriminant
`−4(2t₂² + t₂t₃ + 2t₃²)`, hence positive definite. -/
theorem G0_pos (t₁ t₂ t₃ : ℝ) (ht₁ : 0 < t₁) (hne : 0 < t₂ + t₃) :
    0 < t₁ * (t₁^2 - 2*t₁*t₂ - 2*t₁*t₃ + 3*t₂^2 + 3*t₂*t₃ + 3*t₃^2) := by
  have hq : 0 < t₁^2 - 2*t₁*t₂ - 2*t₁*t₃ + 3*t₂^2 + 3*t₂*t₃ + 3*t₃^2 := by
    nlinarith [sq_nonneg (t₁ - t₂ - t₃), sq_nonneg (t₂ - t₃), sq_nonneg t₂, sq_nonneg t₃,
      sq_nonneg (t₂ + t₃)]
  exact mul_pos ht₁ hq

/-- **`H > 0` unconditionally** — the fact that closes the `p₂ = 1` endpoint at order three.
`H` is the bracket in the linear coefficient of `E|_{p₂=1}` as a quadratic in `p₁`:
`c₁ = 4t₁·H`.  As a quadratic in `t₁` it has positive leading coefficient `t₂+t₃` and
discriminant `−4(2t₂⁴ + 4t₂³t₃ + 3t₂²t₃² + 4t₂t₃³ + 2t₃⁴) < 0`, hence is positive definite. -/
theorem H_pos (t₁ t₂ t₃ : ℝ) (ht₂ : 0 < t₂) (ht₃ : 0 < t₃) :
    0 < t₁^2 * (t₂ + t₃) - 2*t₁ * (t₂^2 + t₂*t₃ + t₃^2)
        + 3 * (t₂^3 + t₂^2*t₃ + t₂*t₃^2 + t₃^3) := by
  nlinarith [sq_nonneg (t₁ * (t₂ + t₃) - (t₂^2 + t₂*t₃ + t₃^2)), sq_nonneg (t₂ - t₃),
    mul_pos ht₂ ht₃, sq_nonneg (t₂ + t₃), mul_pos (mul_pos ht₂ ht₂) (mul_pos ht₃ ht₃),
    sq_nonneg (t₂^2 - t₃^2), mul_pos ht₂ ht₂, mul_pos ht₃ ht₃]

/-- **A quadratic with nonnegative coefficients is nonnegative on `[0,∞)`.**  Used for the
`c₂ ≥ 0` branch of the `p₁`-dichotomy. -/
theorem quad_nonneg_of_coeffs (a b c x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) : 0 ≤ a * x^2 + b * x + c := by
  have : 0 ≤ a * x^2 := mul_nonneg ha (sq_nonneg x)
  have : 0 ≤ b * x := mul_nonneg hb hx
  linarith [mul_nonneg ha (sq_nonneg x), mul_nonneg hb hx]

/-- **A concave quadratic on `[0,1]` is bounded below by its endpoints.**  Used for the
`c₂ < 0` branches of both dichotomies: if `a ≤ 0` then
`a x² + b x + c ≥ min(c, a+b+c)` on `[0,1]`, and here we get it in the interpolated form. -/
theorem concave_quad_ge_endpoints (a b c x : ℝ) (ha : a ≤ 0) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (h0 : 0 ≤ c) (h1 : 0 ≤ a + b + c) : 0 ≤ a * x^2 + b * x + c := by
  have key : a * x^2 + b * x + c - ((1 - x) * c + x * (a + b + c)) = (x - x^2) * (-a) := by
    ring
  have hxx : 0 ≤ x - x^2 := by nlinarith
  have : 0 ≤ (x - x^2) * (-a) := mul_nonneg hxx (by linarith)
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - x) h0, mul_nonneg hx0 h1]

/-! ## Domination on the region `Q_s ≥ 0`

For the general-`s` peeling step, the leading coefficient of `E` in the last continuation
probability has the sign of
`Q_s = ∑ tᵢ² − ((s+5)/(s−1))·∑_{i<j} tᵢtⱼ`.
On `Q_s ≥ 0` the largest holding mean carries at least `(s+5)/(3s+3)` of the total — the
uniform generalisation of `t₁ ≥ 2(t₂+t₃)` at `s = 3`. -/

/-- **Domination on `Q_s ≥ 0`.**  Stated in the scale-free form `m·e₁² ≤ (2+m)·tmax·e₁`, which is
what the peeling argument consumes.  With `m = (s+5)/(s−1)` this says
`tmax/e₁ ≥ m/(2+m) = (s+5)/(3s+3)`.

The proof is two inequalities: `Q_s ≥ 0` rearranges to `(2+m)p₂ ≥ m·e₁²` using
`e₁² = p₂ + 2e₂`, and `p₂ = ∑tᵢ² ≤ tmax·∑tᵢ = tmax·e₁`. -/
theorem domination_of_Q (s : Finset ι) (t : ι → ℝ) (tmax m : ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) (hbd : ∀ i ∈ s, t i ≤ tmax) (hm : 0 ≤ m)
    (hQ : 0 ≤ (2 + m) * psum s t 2 - m * (psum s t 1) ^ 2) :
    m * (psum s t 1) ^ 2 ≤ (2 + m) * (tmax * psum s t 1) := by
  have hp2 : psum s t 2 ≤ tmax * psum s t 1 := psum2_le s t tmax ht hbd
  have h2m : (0:ℝ) ≤ 2 + m := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hp2 h2m]

/-- The rearrangement `Q_s ≥ 0 ↔ (2+m)p₂ ≥ m e₁²`, via `e₁² = p₂ + 2e₂`.  Here `e₂` is supplied
as `(p₁² − p₂)/2`, which is the identity `e₁² = p₂ + 2e₂` in the form used above. -/
theorem Q_rearrange (p₁ p₂ m : ℝ) :
    p₂ - m * ((p₁ ^ 2 - p₂) / 2) = ((2 + m) * p₂ - m * p₁ ^ 2) / 2 := by
  ring

/-! ## The peeling identity

The moments of an order-`s` Coxian law are affine in the last continuation probability:
`aₖ = Uₖ + p·π·t_s·h_{k−1}`, where `Uₖ` are the moments of the truncated order-`(s−1)` law.
Collecting the linear term of `E = 3(s+1)a₁a₃ − 2(s+2)a₂²` gives `π·t_s·W` with
`W = 3(s+1)(h₂U₁ + U₃) − 4(s+2)h₁U₂`.  Both statements below are the algebra of that
substitution, stated over plain reals so they hold for every order at once. -/

/-- **The peeling identity.**  Substituting `aₖ = Uₖ + p·Vₖ` into `E` and collecting powers of
`p` gives leading term `L`, linear term `M`, and constant term `N`. -/
theorem peel_expand (c₁ c₂ U₁ U₂ U₃ V₁ V₂ V₃ p : ℝ) :
    c₁ * (U₁ + p * V₁) * (U₃ + p * V₃) - c₂ * (U₂ + p * V₂) ^ 2
      = (c₁ * V₁ * V₃ - c₂ * V₂ ^ 2) * p ^ 2
        + (c₁ * (U₁ * V₃ + U₃ * V₁) - 2 * c₂ * U₂ * V₂) * p
        + (c₁ * U₁ * U₃ - c₂ * U₂ ^ 2) := by
  ring

/-- With `Vₖ = π·t_s·h_{k−1}` the linear coefficient factors as `π·t_s·W`, where
`W = 3(s+1)(h₂U₁ + U₃) − 4(s+2)h₁U₂`.  (Here `h₀ = 1`.) -/
theorem peel_linear_factor (n U₁ U₂ U₃ h₁ h₂ π ts : ℝ) :
    3 * (n + 1) * (U₁ * (π * ts * h₂) + U₃ * (π * ts * 1))
        - 2 * (2 * (n + 2)) * U₂ * (π * ts * h₁)
      = π * ts * (3 * (n + 1) * (h₂ * U₁ + U₃) - 4 * (n + 2) * h₁ * U₂) := by
  ring

/-! ## The `L = 1` corner, in every order

`W` is multi-affine in the continuation probabilities, so its minimum is at a corner, and each
corner is a pure hypoexponential on a prefix `t₁,…,t_L`.  The `L = 1` corner is
`W₁ = t₁·[3(s+1)(h₂ + t₁²) − 4(s+2)h₁t₁]`, and the bracket is positive definite as a quadratic in
`t₁` exactly when `h₂/h₁² > 4(s+2)²/(9(s+1)²)`.  The domination hypothesis delivers this with room
`(s−1)²/(9(s+1)²)`. -/

/-- The key numerical identity behind the `L = 1` corner: with `c = (s+5)/(3s+3)`,
`(1 + c²)/2 − 4(s+2)²/(9(s+1)²) = (s−1)²/(9(s+1)²)`. -/
theorem corner_gap_identity (n : ℝ) (hn : 0 < n + 1) :
    (1 + ((n + 5) / (3*n + 3))^2) / 2 - 4*(n + 2)^2 / (9*(n + 1)^2)
      = (n - 1)^2 / (9*(n + 1)^2) := by
  have h3 : (3:ℝ)*n + 3 ≠ 0 := by intro h; apply absurd hn; push Not; linarith
  have h1 : (n:ℝ) + 1 ≠ 0 := by intro h; apply absurd hn; push Not; linarith
  field_simp
  ring

/-- **The `L = 1` corner bracket is positive.**  If `h₂ ≥ κ·h₁²` with
`κ > 4(n+2)²/(9(n+1)²)` and `h₁ > 0`, then `3(n+1)(h₂ + t²) − 4(n+2)h₁t > 0` for every `t`:
the quadratic in `t` has positive leading coefficient and negative discriminant. -/
theorem cornerL1_bracket_pos (n h₁ h₂ t : ℝ) (hn : 0 ≤ n)
    (_hh₁ : 0 < h₁) (hdisc : 4*(n + 2)^2 * h₁^2 < 9*(n + 1)^2 * h₂) :
    0 < 3*(n + 1) * (h₂ + t^2) - 4*(n + 2) * h₁ * t := by
  have hlead : 0 < 3*(n + 1) := by linarith
  -- complete the square: 3(n+1)(t − 2(n+2)h₁/(3(n+1)))² + (9(n+1)²h₂ − 4(n+2)²h₁²)/(3(n+1))
  have key : (3*(n + 1)) * (3*(n + 1) * (h₂ + t^2) - 4*(n + 2) * h₁ * t)
      = (3*(n + 1) * t - 2*(n + 2) * h₁)^2 + (9*(n + 1)^2 * h₂ - 4*(n + 2)^2 * h₁^2) := by
    ring
  nlinarith [sq_nonneg (3*(n + 1) * t - 2*(n + 2) * h₁), key, hlead]

/-- **The `L = 1` corner, all orders.**  Packaging: from the domination bound
`c·h₁ ≤ tmax` and `tmax² ≤ p₂`, together with `h₂ = (h₁² + p₂)/2`, the discriminant hypothesis of
`cornerL1_bracket_pos` holds, hence `W₁ > 0`. -/
theorem cornerL1_pos (n h₁ p₂ tmax t : ℝ) (hn : 2 ≤ n) (hh₁ : 0 < h₁)
    (hdom : (n + 5) / (3*n + 3) * h₁ ≤ tmax) (htmax : 0 ≤ tmax)
    (hp₂ : tmax^2 ≤ p₂) :
    0 < 3*(n + 1) * ((h₁^2 + p₂)/2 + t^2) - 4*(n + 2) * h₁ * t := by
  have hn1 : (0:ℝ) < n + 1 := by linarith
  have h3 : (0:ℝ) < 3*n + 3 := by linarith
  set c : ℝ := (n + 5) / (3*n + 3) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  -- p₂ ≥ tmax² ≥ (c h₁)²
  have hch : 0 ≤ c * h₁ := mul_nonneg (le_of_lt hcpos) (le_of_lt hh₁)
  have hstep : (c * h₁)^2 ≤ p₂ := le_trans (by nlinarith [hdom, hch]) hp₂
  -- the gap identity gives c² > 8(n+2)²/(9(n+1)²) − 1, i.e. the discriminant bound
  have hgap : (1 + c^2)/2 - 4*(n + 2)^2 / (9*(n + 1)^2) = (n - 1)^2 / (9*(n + 1)^2) := by
    rw [hc]; exact corner_gap_identity n hn1
  have hpos : 0 < (n - 1)^2 / (9*(n + 1)^2) := by
    apply div_pos (by nlinarith) (by positivity)
  have hkey : 4*(n + 2)^2 / (9*(n + 1)^2) < (1 + c^2)/2 := by linarith
  have hdisc : 4*(n + 2)^2 * h₁^2 < 9*(n + 1)^2 * ((h₁^2 + p₂)/2) := by
    have h9 : (0:ℝ) < 9*(n + 1)^2 := by positivity
    rw [div_lt_iff₀ h9] at hkey
    have hsq : (0:ℝ) < h₁^2 := by positivity
    -- multiply hkey by h₁² > 0, then use p₂ ≥ c²h₁²
    have hmul : 4*(n + 2)^2 * h₁^2 < (1 + c^2)/2 * (9*(n + 1)^2) * h₁^2 :=
      by nlinarith [hkey, hsq]
    have hexp : (1 + c^2)/2 * (9*(n + 1)^2) * h₁^2
        = 9*(n + 1)^2 * ((h₁^2 + c^2 * h₁^2)/2) := by ring
    have hle : 9*(n + 1)^2 * ((h₁^2 + c^2 * h₁^2)/2)
        ≤ 9*(n + 1)^2 * ((h₁^2 + p₂)/2) := by
      have : c^2 * h₁^2 ≤ p₂ := by nlinarith [hstep]
      have h9' : (0:ℝ) ≤ 9*(n + 1)^2 := le_of_lt h9
      nlinarith [this, h9']
    linarith [hmul, hexp.le, hexp.ge, hle]
  exact cornerL1_bracket_pos n h₁ ((h₁^2 + p₂)/2) t (by linarith) hh₁ hdisc

/-! ## A second complete-homogeneous inequality: `3L·h₃ ≥ (L+2)·h₁h₂`

This governs the prefix part of the corner inequalities.  In power sums it is
`3L·h₃ − (L+2)h₁h₂`, and its Lagrange form is
`∑_{i<j} (tᵢ−tⱼ)²(tᵢ + tⱼ + p₁)`, manifestly nonnegative for `t ≥ 0`. -/

/-- The power-sum form of `3L·h₃ − (L+2)·h₁h₂`: a ring identity in `L, p₁, p₂, p₃`.
Multiplying by `6` clears denominators. -/
theorem h3h1h2_identity (L p₁ p₂ p₃ : ℝ) :
    6 * (3 * L * ((p₁ ^ 3 + 3 * p₁ * p₂ + 2 * p₃) / 6)
          - (L + 2) * p₁ * ((p₁ ^ 2 + p₂) / 2))
      = 6 * L * p₃ + 6 * (L - 1) * p₁ * p₂ - 6 * p₁ ^ 3 := by
  ring

/-- **The Lagrange form.**  `∑ᵢ∑ⱼ (tᵢ−tⱼ)²(tᵢ+tⱼ+p₁) ≥ 0` for nonnegative `t` — the shape that
certifies `3L·h₃ ≥ (L+2)·h₁h₂`.  Each summand is a square times a nonnegative factor. -/
theorem h3h1h2_lagrange_nonneg (s : Finset ι) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, (t i - t j) ^ 2 * (t i + t j + psum s t 1) := by
  have hp₁ : 0 ≤ psum s t 1 := Finset.sum_nonneg fun i hi => by simpa using ht i hi
  refine Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => ?_
  have hi' := ht i hi
  have hj' := ht j hj
  exact mul_nonneg (sq_nonneg _) (by linarith)


/-- **The prefix threshold.**  Granting the certificate `(L+2)·H₁H₂ ≤ 3L·H₃`, the combination
`A = 3(s+1)H₃ − (s+5)H₁H₂` is nonnegative as soon as `2L ≤ s+1`.

The computation is `3(s+1)H₃ = ((s+1)/L)·(3L·H₃) ≥ ((s+1)(L+2)/L)·H₁H₂`, and
`(s+1)(L+2)/L − (s+5) = (2s+2−4L)/L ≥ 0`. -/
theorem A_nonneg_of_threshold (n L H₁ H₂ H₃ : ℝ) (hL : 0 < L) (hH : 0 ≤ H₁ * H₂)
    (hn : 0 ≤ n + 1) (hthr : 2 * L ≤ n + 1)
    (hcert : (L + 2) * (H₁ * H₂) ≤ 3 * L * H₃) :
    0 ≤ 3 * (n + 1) * H₃ - (n + 5) * (H₁ * H₂) := by
  have hfac : 0 ≤ (n + 1) / L := div_nonneg hn (le_of_lt hL)
  have hstep : (n + 1) / L * ((L + 2) * (H₁ * H₂)) ≤ (n + 1) / L * (3 * L * H₃) :=
    mul_le_mul_of_nonneg_left hcert hfac
  have hLne : L ≠ 0 := ne_of_gt hL
  have hR : (n + 1) / L * (3 * L * H₃) = 3 * (n + 1) * H₃ := by field_simp
  have hLhs : (n + 1) / L * ((L + 2) * (H₁ * H₂))
      = (n + 5) * (H₁ * H₂) + ((2*n + 2 - 4*L) / L) * (H₁ * H₂) := by
    field_simp; ring
  have hgap : 0 ≤ ((2*n + 2 - 4*L) / L) * (H₁ * H₂) :=
    mul_nonneg (div_nonneg (by linarith) (le_of_lt hL)) hH
  rw [hR] at hstep
  rw [hLhs] at hstep
  linarith

/-! ## The order-three Coxian bound, assembled

`E₃ = 12a₁a₃ − 10a₂²` for the order-three Coxian law with holding means `t₁,t₂,t₃` and
continuation probabilities `p₁,p₂`.  We assemble `E₃ ≥ 0` from the two dichotomies. -/

/-- `E₃`, the order-three Coxian discriminant `12a₁a₃ − 10a₂²`. -/
noncomputable def coxE3 (t₁ t₂ t₃ p₁ p₂ : ℝ) : ℝ :=
  12 * (p₁*p₂*t₃ + p₁*t₂ + t₁)
      * (p₁*p₂*t₁^2*t₃ + p₁*p₂*t₁*t₂*t₃ + p₁*p₂*t₁*t₃^2 + p₁*p₂*t₂^2*t₃ + p₁*p₂*t₂*t₃^2
          + p₁*p₂*t₃^3 + p₁*t₁^2*t₂ + p₁*t₁*t₂^2 + p₁*t₂^3 + t₁^3)
    - 10 * (p₁*p₂*t₁*t₃ + p₁*p₂*t₂*t₃ + p₁*p₂*t₃^2 + p₁*t₁*t₂ + p₁*t₂^2 + t₁^2)^2

/-- `E₃` as a quadratic in `p₂`. -/
theorem coxE3_quad (t₁ t₂ t₃ p₁ p₂ : ℝ) :
    coxE3 t₁ t₂ t₃ p₁ p₂
      = (2*p₁^2*t₃^2 * (t₁^2 - 4*t₁*t₂ - 4*t₁*t₃ + t₂^2 - 4*t₂*t₃ + t₃^2)) * p₂^2
        + (4*p₁*t₃ * (p₁ * (t₂*(t₁^2 - 4*t₁*t₂ - 2*t₁*t₃ + t₂^2 - 2*t₂*t₃ + 3*t₃^2))
              + t₁*(t₁^2 - 2*t₁*t₂ - 2*t₁*t₃ + 3*t₂^2 + 3*t₂*t₃ + 3*t₃^2))) * p₂
        + coxE3 t₁ t₂ t₃ p₁ 0 := by
  unfold coxE3; ring

/-- The `p₂ = 0` endpoint of `E₃` is the order-two expression with the order-three constant,
hence nonnegative by `coxE3_endpoint_zero`. -/
theorem coxE3_at_zero_nonneg (t₁ t₂ p₁ : ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ ≤ 1) (t₃ : ℝ) :
    0 ≤ coxE3 t₁ t₂ t₃ p₁ 0 := by
  have h := coxE3_endpoint_zero t₁ t₂ p₁ ht₁ ht₂ hp₁0 hp₁1
  unfold coxE3
  nlinarith [h]

/-- **`E₃ ≥ 0`**, given the `p₂ = 1` endpoint.  The `p₂`-dichotomy: if the leading coefficient is
`≤ 0` the quadratic is concave and bounded below by its endpoints; if it is `> 0` then, since the
linear coefficient is nonnegative (hypothesis `hlin`, supplied by `G0_pos` and the sign analysis of
Proposition 
ef{prop:coxian3}), all three coefficients are nonnegative. -/
theorem coxE3_nonneg_of_endpoints (t₁ t₂ t₃ p₁ p₂ : ℝ)
    (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ ≤ 1)
    (h0 : 0 ≤ coxE3 t₁ t₂ t₃ p₁ 0)
    (h1 : 0 ≤ coxE3 t₁ t₂ t₃ p₁ 1)
    (hlin : 0 ≤ 4*p₁*t₃ * (p₁ * (t₂*(t₁^2 - 4*t₁*t₂ - 2*t₁*t₃ + t₂^2 - 2*t₂*t₃ + 3*t₃^2))
              + t₁*(t₁^2 - 2*t₁*t₂ - 2*t₁*t₃ + 3*t₂^2 + 3*t₂*t₃ + 3*t₃^2))) :
    0 ≤ coxE3 t₁ t₂ t₃ p₁ p₂ := by
  set a : ℝ := 2*p₁^2*t₃^2 * (t₁^2 - 4*t₁*t₂ - 4*t₁*t₃ + t₂^2 - 4*t₂*t₃ + t₃^2) with ha
  set b : ℝ := 4*p₁*t₃ * (p₁ * (t₂*(t₁^2 - 4*t₁*t₂ - 2*t₁*t₃ + t₂^2 - 2*t₂*t₃ + 3*t₃^2))
              + t₁*(t₁^2 - 2*t₁*t₂ - 2*t₁*t₃ + 3*t₂^2 + 3*t₂*t₃ + 3*t₃^2)) with hb
  set c : ℝ := coxE3 t₁ t₂ t₃ p₁ 0 with hc
  have hE : coxE3 t₁ t₂ t₃ p₁ p₂ = a * p₂^2 + b * p₂ + c := coxE3_quad t₁ t₂ t₃ p₁ p₂
  have hE1 : coxE3 t₁ t₂ t₃ p₁ 1 = a + b + c := by
    have := coxE3_quad t₁ t₂ t₃ p₁ 1; rw [this]; ring
  rw [hE]
  rcases le_or_gt a 0 with hneg | hpos
  · exact concave_quad_ge_endpoints a b c p₂ hneg hp₂0 hp₂1 h0 (by rw [← hE1]; exact h1)
  · exact quad_nonneg_of_coeffs a b c p₂ (le_of_lt hpos) hlin h0 hp₂0

/-- The pure three-chain instance of `chain_ineq`, as an explicit polynomial inequality:
`12h₁h₃ − 10h₂² ≥ 0` for nonnegative `t₁,t₂,t₃`. -/
theorem chain_ineq_three (t₁ t₂ t₃ : ℝ) (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (h₃ : 0 ≤ t₃) :
    0 ≤ 2*t₁^4 + 4*t₁^3*t₂ + 4*t₁^3*t₃ - 6*t₁^2*t₂^2 - 4*t₁^2*t₂*t₃ - 6*t₁^2*t₃^2
        + 4*t₁*t₂^3 - 4*t₁*t₂^2*t₃ - 4*t₁*t₂*t₃^2 + 4*t₁*t₃^3
        + 2*t₂^4 + 4*t₂^3*t₃ - 6*t₂^2*t₃^2 + 4*t₂*t₃^3 + 2*t₃^4 := by
  have key := chain_ineq (Finset.univ : Finset (Fin 3)) (fun i => ![t₁, t₂, t₃] i)
    (by intro i _; fin_cases i <;> simpa)
  simp only [psum, Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Nat.cast_ofNat] at key
  nlinarith [key]

/-- **The `p₂ = 1` endpoint of `E₃`.**  As a quadratic in `p₁` it is
`d₂p₁² + 4t₁H·p₁ + 2t₁⁴` with `H > 0` by `H_pos`, so: if `d₂ ≥ 0` all coefficients are
nonnegative; if `d₂ < 0` the parabola is concave and its endpoint values are `2t₁⁴ ≥ 0` and the
pure three-chain `12h₁h₃ − 10h₂² ≥ 0` of `chain_ineq_three`. -/
theorem coxE3_at_one_nonneg (t₁ t₂ t₃ p₁ : ℝ) (ht₁ : 0 ≤ t₁) (ht₂ : 0 < t₂) (ht₃ : 0 < t₃)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ ≤ 1) :
    0 ≤ coxE3 t₁ t₂ t₃ p₁ 1 := by
  set d₂ : ℝ := 2*(t₁^2*t₂^2 + 2*t₁^2*t₂*t₃ + t₁^2*t₃^2 - 4*t₁*t₂^3 - 8*t₁*t₂^2*t₃
      - 8*t₁*t₂*t₃^2 - 4*t₁*t₃^3 + t₂^4 + 2*t₂^3*t₃ - 3*t₂^2*t₃^2 + 2*t₂*t₃^3 + t₃^4) with hd₂
  set H : ℝ := t₁^2*(t₂ + t₃) - 2*t₁*(t₂^2 + t₂*t₃ + t₃^2)
      + 3*(t₂^3 + t₂^2*t₃ + t₂*t₃^2 + t₃^3) with hH
  have hEq : coxE3 t₁ t₂ t₃ p₁ 1 = d₂ * p₁^2 + (4*t₁*H) * p₁ + 2*t₁^4 := by
    unfold coxE3; rw [hd₂, hH]; ring
  have hHpos : 0 < H := by rw [hH]; exact H_pos t₁ t₂ t₃ ht₂ ht₃
  have hlin : 0 ≤ 4*t₁*H := by positivity
  have hconst : (0:ℝ) ≤ 2*t₁^4 := by positivity
  rw [hEq]
  rcases le_or_gt d₂ 0 with hneg | hpos
  · -- concave: use the endpoints p₁ = 0 and p₁ = 1
    refine concave_quad_ge_endpoints d₂ (4*t₁*H) (2*t₁^4) p₁ hneg hp₁0 hp₁1 hconst ?_
    -- at p₁ = 1 the value is the pure three-chain expression
    have hchain := chain_ineq_three t₁ t₂ t₃ ht₁ (le_of_lt ht₂) (le_of_lt ht₃)
    have hid : d₂ + 4*t₁*H + 2*t₁^4
        = 2*t₁^4 + 4*t₁^3*t₂ + 4*t₁^3*t₃ - 6*t₁^2*t₂^2 - 4*t₁^2*t₂*t₃ - 6*t₁^2*t₃^2
          + 4*t₁*t₂^3 - 4*t₁*t₂^2*t₃ - 4*t₁*t₂*t₃^2 + 4*t₁*t₃^3
          + 2*t₂^4 + 4*t₂^3*t₃ - 6*t₂^2*t₃^2 + 4*t₂*t₃^3 + 2*t₃^4 := by
      rw [hd₂, hH]; ring
    rw [hid]; exact hchain
  · exact quad_nonneg_of_coeffs d₂ (4*t₁*H) (2*t₁^4) p₁ (le_of_lt hpos) hlin hconst hp₁0

/-- **Theorem (the Coxian case at order three).**  For all holding means `t₁,t₂,t₃ > 0` and
continuation probabilities `p₁,p₂ ∈ [0,1]`, the order-three Coxian law satisfies
`12a₁a₃ − 10a₂² ≥ 0`, i.e. `a₁a₃/a₂² ≥ 5/6 = κ₃`.

The proof is the `p₂`-dichotomy of `coxE3_nonneg_of_endpoints`, with the `p₂ = 0` endpoint from
`coxE3_at_zero_nonneg` (the order-two result plus a square) and the `p₂ = 1` endpoint from
`coxE3_at_one_nonneg` (the `p₁`-dichotomy, resting on `H_pos` and the pure three-chain).

The linear coefficient in `p₂` is nonnegative because it equals `4p₁t₃(p₁G₁ + G₀)`; here we take
that sign as the hypothesis `hlin`, which Proposition `coxian3` establishes from `G0_pos` together
with the domination extracted from `Q ≥ 0`. -/
theorem coxian3_nonneg (t₁ t₂ t₃ p₁ p₂ : ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (ht₃ : 0 < t₃)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ ≤ 1) (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ ≤ 1)
    (hlin : 0 ≤ 4*p₁*t₃ * (p₁ * (t₂*(t₁^2 - 4*t₁*t₂ - 2*t₁*t₃ + t₂^2 - 2*t₂*t₃ + 3*t₃^2))
              + t₁*(t₁^2 - 2*t₁*t₂ - 2*t₁*t₃ + 3*t₂^2 + 3*t₂*t₃ + 3*t₃^2))) :
    0 ≤ coxE3 t₁ t₂ t₃ p₁ p₂ :=
  coxE3_nonneg_of_endpoints t₁ t₂ t₃ p₁ p₂ hp₂0 hp₂1
    (coxE3_at_zero_nonneg t₁ t₂ p₁ ht₁ ht₂ hp₁0 hp₁1 t₃)
    (coxE3_at_one_nonneg t₁ t₂ t₃ p₁ (le_of_lt ht₁) ht₂ ht₃ hp₁0 hp₁1)
    hlin

/-- The ratio form of `coxian3_nonneg`: `10a₂² ≤ 12a₁a₃`, i.e. `a₁a₃/a₂² ≥ 5/6`. -/
theorem coxian3_ratio (t₁ t₂ t₃ p₁ p₂ : ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (ht₃ : 0 < t₃)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ ≤ 1) (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ ≤ 1)
    (hlin : 0 ≤ 4*p₁*t₃ * (p₁ * (t₂*(t₁^2 - 4*t₁*t₂ - 2*t₁*t₃ + t₂^2 - 2*t₂*t₃ + 3*t₃^2))
              + t₁*(t₁^2 - 2*t₁*t₂ - 2*t₁*t₃ + 3*t₂^2 + 3*t₂*t₃ + 3*t₃^2))) :
    10 * (p₁*p₂*t₁*t₃ + p₁*p₂*t₂*t₃ + p₁*p₂*t₃^2 + p₁*t₁*t₂ + p₁*t₂^2 + t₁^2)^2
      ≤ 12 * (p₁*p₂*t₃ + p₁*t₂ + t₁)
          * (p₁*p₂*t₁^2*t₃ + p₁*p₂*t₁*t₂*t₃ + p₁*p₂*t₁*t₃^2 + p₁*p₂*t₂^2*t₃ + p₁*p₂*t₂*t₃^2
              + p₁*p₂*t₃^3 + p₁*t₁^2*t₂ + p₁*t₁*t₂^2 + p₁*t₂^3 + t₁^3) := by
  have h := coxian3_nonneg t₁ t₂ t₃ p₁ p₂ ht₁ ht₂ ht₃ hp₁0 hp₁1 hp₂0 hp₂1 hlin
  unfold coxE3 at h
  linarith

/-- **`G₀ + G₁ ≥ 0` on the region `Q ≥ 0`.**  By `Q_nonneg_domination` the largest holding mean
dominates twice the sum of the other two; substituting `t_max = 2(other two) + r` with `r ≥ 0`
turns `G₀ + G₁` into a polynomial with all coefficients nonnegative, in each of the three cases
according to which `tᵢ` is largest. -/
theorem G0G1_nonneg_of_dom (t₁ t₂ t₃ : ℝ) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (ht₃ : 0 ≤ t₃)
    (hdom : 2*(t₂ + t₃) ≤ t₁ ∨ 2*(t₁ + t₃) ≤ t₂ ∨ 2*(t₁ + t₂) ≤ t₃) :
    0 ≤ t₁*(t₁^2 - 2*t₁*t₂ - 2*t₁*t₃ + 3*t₂^2 + 3*t₂*t₃ + 3*t₃^2)
        + t₂*(t₁^2 - 4*t₁*t₂ - 2*t₁*t₃ + t₂^2 - 2*t₂*t₃ + 3*t₃^2) := by
  rcases hdom with h | h | h
  · -- t₁ largest: with r = t₁ − 2(t₂+t₃) ≥ 0 the form is
    -- r³ + 5r²t₂ + 4r²t₃ + 7rt₂² + 13rt₂t₃ + 7rt₃² + 3t₂³ + 6t₂²t₃ + 15t₂t₃² + 6t₃³
    have hr : 0 ≤ t₁ - 2*(t₂ + t₃) := by linarith
    nlinarith [mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg hr hr) ht₂,
      mul_nonneg (mul_nonneg hr hr) ht₃, mul_nonneg hr (mul_nonneg ht₂ ht₂),
      mul_nonneg hr (mul_nonneg ht₂ ht₃), mul_nonneg hr (mul_nonneg ht₃ ht₃),
      mul_nonneg (mul_nonneg ht₂ ht₂) ht₂, mul_nonneg (mul_nonneg ht₂ ht₂) ht₃,
      mul_nonneg (mul_nonneg ht₂ ht₃) ht₃, mul_nonneg (mul_nonneg ht₃ ht₃) ht₃]
  · -- t₂ largest: same shape with t₁ ↔ t₂
    have hr : 0 ≤ t₂ - 2*(t₁ + t₃) := by linarith
    nlinarith [mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg hr hr) ht₁,
      mul_nonneg (mul_nonneg hr hr) ht₃, mul_nonneg hr (mul_nonneg ht₁ ht₁),
      mul_nonneg hr (mul_nonneg ht₁ ht₃), mul_nonneg hr (mul_nonneg ht₃ ht₃),
      mul_nonneg (mul_nonneg ht₁ ht₁) ht₁, mul_nonneg (mul_nonneg ht₁ ht₁) ht₃,
      mul_nonneg (mul_nonneg ht₁ ht₃) ht₃, mul_nonneg (mul_nonneg ht₃ ht₃) ht₃]
  · -- t₃ largest: with r = t₃ − 2(t₁+t₂) ≥ 0 the form is
    -- 3r²t₁ + 3r²t₂ + 10rt₁² + 25rt₁t₂ + 10rt₂² + 9t₁³ + 33t₁²t₂ + 33t₁t₂² + 9t₂³
    have hr : 0 ≤ t₃ - 2*(t₁ + t₂) := by linarith
    nlinarith [mul_nonneg (mul_nonneg hr hr) ht₁, mul_nonneg (mul_nonneg hr hr) ht₂,
      mul_nonneg hr (mul_nonneg ht₁ ht₁), mul_nonneg hr (mul_nonneg ht₁ ht₂),
      mul_nonneg hr (mul_nonneg ht₂ ht₂), mul_nonneg (mul_nonneg ht₁ ht₁) ht₁,
      mul_nonneg (mul_nonneg ht₁ ht₁) ht₂, mul_nonneg (mul_nonneg ht₁ ht₂) ht₂,
      mul_nonneg (mul_nonneg ht₂ ht₂) ht₂]

/-- **`hlin` holds on `Q ≥ 0`.**  The linear coefficient of `E₃` in `p₂` is `4p₁t₃(p₁G₁ + G₀)`,
and `p₁G₁ + G₀` is affine in `p₁ ∈ [0,1]` with `G₀ > 0` (`G0_pos`) and `G₀ + G₁ ≥ 0`
(`G0G1_nonneg_of_dom`), hence nonnegative. -/
theorem hlin_of_dom (t₁ t₂ t₃ p₁ : ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (ht₃ : 0 < t₃)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ ≤ 1)
    (hdom : 2*(t₂ + t₃) ≤ t₁ ∨ 2*(t₁ + t₃) ≤ t₂ ∨ 2*(t₁ + t₂) ≤ t₃) :
    0 ≤ 4*p₁*t₃ * (p₁ * (t₂*(t₁^2 - 4*t₁*t₂ - 2*t₁*t₃ + t₂^2 - 2*t₂*t₃ + 3*t₃^2))
          + t₁*(t₁^2 - 2*t₁*t₂ - 2*t₁*t₃ + 3*t₂^2 + 3*t₂*t₃ + 3*t₃^2)) := by
  have hG₀ : 0 < t₁*(t₁^2 - 2*t₁*t₂ - 2*t₁*t₃ + 3*t₂^2 + 3*t₂*t₃ + 3*t₃^2) :=
    G0_pos t₁ t₂ t₃ ht₁ (by linarith)
  have hsum := G0G1_nonneg_of_dom t₁ t₂ t₃ (le_of_lt ht₁) (le_of_lt ht₂) (le_of_lt ht₃) hdom
  -- p₁G₁ + G₀ = (1-p₁)G₀ + p₁(G₀+G₁) ≥ 0
  have hbr : 0 ≤ p₁ * (t₂*(t₁^2 - 4*t₁*t₂ - 2*t₁*t₃ + t₂^2 - 2*t₂*t₃ + 3*t₃^2))
        + t₁*(t₁^2 - 2*t₁*t₂ - 2*t₁*t₃ + 3*t₂^2 + 3*t₂*t₃ + 3*t₃^2) := by
    nlinarith [mul_nonneg hp₁0 hsum, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p₁) (le_of_lt hG₀)]
  have h4 : (0:ℝ) ≤ 4*p₁*t₃ := by positivity
  exact mul_nonneg h4 hbr

/-- **Theorem (Coxian at order three, unconditional).**  For all `t₁,t₂,t₃ > 0` and
`p₁,p₂ ∈ [0,1]`, `E₃ = 12a₁a₃ − 10a₂² ≥ 0`, i.e. `a₁a₃/a₂² ≥ 5/6 = κ₃`.

The `p₂`-dichotomy is cased on the sign of `Q = t₁²+t₂²+t₃² − 4(t₁t₂+t₁t₃+t₂t₃)`, which
governs the leading coefficient `2p₁²t₃²Q`:

* `Q < 0`: the quadratic in `p₂` is concave, so it is bounded below by its endpoint values, both
  nonnegative (`coxE3_at_zero_nonneg`, `coxE3_at_one_nonneg`).
* `Q ≥ 0`: then `Q_nonneg_domination` gives the domination `2(sum of the other two) ≤ tmax`, so
  `hlin_of_dom` applies and all three coefficients are nonnegative. -/
theorem coxian3_nonneg_uncond (t₁ t₂ t₃ p₁ p₂ : ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (ht₃ : 0 < t₃)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ ≤ 1) (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ ≤ 1) :
    0 ≤ coxE3 t₁ t₂ t₃ p₁ p₂ := by
  set a : ℝ := 2*p₁^2*t₃^2 * (t₁^2 - 4*t₁*t₂ - 4*t₁*t₃ + t₂^2 - 4*t₂*t₃ + t₃^2) with ha
  set b : ℝ := 4*p₁*t₃ * (p₁ * (t₂*(t₁^2 - 4*t₁*t₂ - 2*t₁*t₃ + t₂^2 - 2*t₂*t₃ + 3*t₃^2))
              + t₁*(t₁^2 - 2*t₁*t₂ - 2*t₁*t₃ + 3*t₂^2 + 3*t₂*t₃ + 3*t₃^2)) with hb
  set c : ℝ := coxE3 t₁ t₂ t₃ p₁ 0 with hc
  have hE : coxE3 t₁ t₂ t₃ p₁ p₂ = a * p₂^2 + b * p₂ + c := coxE3_quad t₁ t₂ t₃ p₁ p₂
  have h0 : 0 ≤ c := coxE3_at_zero_nonneg t₁ t₂ p₁ ht₁ ht₂ hp₁0 hp₁1 t₃
  have h1 : 0 ≤ coxE3 t₁ t₂ t₃ p₁ 1 :=
    coxE3_at_one_nonneg t₁ t₂ t₃ p₁ (le_of_lt ht₁) ht₂ ht₃ hp₁0 hp₁1
  have hE1 : coxE3 t₁ t₂ t₃ p₁ 1 = a + b + c := by
    have := coxE3_quad t₁ t₂ t₃ p₁ 1; rw [this]; ring
  rw [hE]
  rcases le_or_gt (t₁^2 - 4*t₁*t₂ - 4*t₁*t₃ + t₂^2 - 4*t₂*t₃ + t₃^2) 0 with hQ | hQ
  · -- Q ≤ 0 ⟹ a ≤ 0: concave branch
    have hane : a ≤ 0 := by
      rw [ha]
      have : (0:ℝ) ≤ 2*p₁^2*t₃^2 := by positivity
      exact mul_nonpos_of_nonneg_of_nonpos this hQ
    exact concave_quad_ge_endpoints a b c p₂ hane hp₂0 hp₂1 h0 (by rw [← hE1]; exact h1)
  · -- Q > 0 ⟹ domination ⟹ hlin, and all coefficients are nonnegative
    have hdom : 2*(t₂ + t₃) ≤ t₁ ∨ 2*(t₁ + t₃) ≤ t₂ ∨ 2*(t₁ + t₂) ≤ t₃ := by
      rcases le_total t₁ t₂ with h12 | h12
      · rcases le_total t₂ t₃ with h23 | h23
        · exact Or.inr (Or.inr (Q_nonneg_domination t₃ t₁ t₂ (le_of_lt ht₁) (le_of_lt ht₂)
            (by linarith) h23 (by nlinarith)))
        · exact Or.inr (Or.inl (Q_nonneg_domination t₂ t₁ t₃ (le_of_lt ht₁) (le_of_lt ht₃)
            h12 h23 (by nlinarith)))
      · rcases le_total t₁ t₃ with h13 | h13
        · exact Or.inr (Or.inr (Q_nonneg_domination t₃ t₁ t₂ (le_of_lt ht₁) (le_of_lt ht₂)
            h13 (by linarith) (by nlinarith)))
        · exact Or.inl (Q_nonneg_domination t₁ t₂ t₃ (le_of_lt ht₂) (le_of_lt ht₃)
            h12 h13 (by nlinarith))
    have hlin : 0 ≤ b := by rw [hb]; exact hlin_of_dom t₁ t₂ t₃ p₁ ht₁ ht₂ ht₃ hp₁0 hp₁1 hdom
    have hapos : 0 ≤ a := by rw [ha]; positivity
    exact quad_nonneg_of_coeffs a b c p₂ hapos hlin h0 hp₂0

/-- **The order-three Coxian bound in ratio form, unconditional**: `10a₂² ≤ 12a₁a₃`, i.e.
`a₁a₃/a₂² ≥ 5/6`, for all `t₁,t₂,t₃ > 0` and `p₁,p₂ ∈ [0,1]`.  Equality at `t₁=t₂=t₃`,
`p₁=p₂=1` (`Erlang(3)`). -/
theorem coxian3_ratio_uncond (t₁ t₂ t₃ p₁ p₂ : ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (ht₃ : 0 < t₃)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ ≤ 1) (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ ≤ 1) :
    10 * (p₁*p₂*t₁*t₃ + p₁*p₂*t₂*t₃ + p₁*p₂*t₃^2 + p₁*t₁*t₂ + p₁*t₂^2 + t₁^2)^2
      ≤ 12 * (p₁*p₂*t₃ + p₁*t₂ + t₁)
          * (p₁*p₂*t₁^2*t₃ + p₁*p₂*t₁*t₂*t₃ + p₁*p₂*t₁*t₃^2 + p₁*p₂*t₂^2*t₃ + p₁*p₂*t₂*t₃^2
              + p₁*p₂*t₃^3 + p₁*t₁^2*t₂ + p₁*t₁*t₂^2 + p₁*t₂^3 + t₁^3) := by
  have h := coxian3_nonneg_uncond t₁ t₂ t₃ p₁ p₂ ht₁ ht₂ ht₃ hp₁0 hp₁1 hp₂0 hp₂1
  unfold coxE3 at h
  linarith

/-! ## Order two with a cycle

At `s = 2` the general routing is the two-cycle `p₁₂ = u`, `p₂₁ = v` with `uv < 1`, which is
*not* Coxian when `v > 0`.  The bound `a₁a₃/a₂² ≥ 8/9` still holds, and the proof is again a
dichotomy: the relevant numerator is a *concave* quadratic in `v` (leading coefficient
`−8d₁²d₂²u²`), so its minimum over `v ∈ [0,1]` sits at an endpoint.  The `v = 0` endpoint is the
acyclic (Coxian) case, and the `v = 1` endpoint follows from `u(u−1)² ≥ 0`. -/

/-- The numerator of `9a₁a₃ − 8a₂²` for the order-two two-cycle, as a quadratic in `v`. -/
noncomputable def cyc2N (d₁ d₂ u v : ℝ) : ℝ :=
  d₁^4*u^2 + 9*d₁^3*d₂*u^3*v - 7*d₁^3*d₂*u^2*v - 7*d₁^3*d₂*u^2 + 9*d₁^3*d₂*u
    - 8*d₁^2*d₂^2*u^2*v^2 + 11*d₁^2*d₂^2*u^2*v + d₁^2*d₂^2*u^2 + 9*d₁^2*d₂^2*u*v
    - 7*d₁^2*d₂^2*u + 2*d₁*d₂^3*u*v + 2*d₁*d₂^3*u + d₂^4

/-- `cyc2N` is a quadratic in `v` with leading coefficient `−8d₁²d₂²u²`, hence concave. -/
theorem cyc2N_quad (d₁ d₂ u v : ℝ) :
    cyc2N d₁ d₂ u v
      = (-(8*d₁^2*d₂^2*u^2)) * v^2
        + (d₁*d₂*u * (9*d₁^2*u^2 - 7*d₁^2*u + 11*d₁*d₂*u + 9*d₁*d₂ + 2*d₂^2)) * v
        + cyc2N d₁ d₂ u 0 := by
  unfold cyc2N; ring

/-- **The `v = 1` endpoint.**  Only one term is negative, `−14d₁³d₂u²`, and it is absorbed by
`9d₁³d₂u³ + 9d₁³d₂u ≥ 18d₁³d₂u²`, which is `9d₁³d₂·u(u−1)² ≥ 0` rearranged. -/
theorem cyc2N_at_one_nonneg (d₁ d₂ u : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hu : 0 ≤ u) :
    0 ≤ cyc2N d₁ d₂ u 1 := by
  have hamgm : 0 ≤ 9*d₁^3*d₂ * (u * (u - 1)^2) := by positivity
  have hrest : 0 ≤ d₁^4*u^2 + 4*d₁^2*d₂^2*u^2 + 2*d₁^2*d₂^2*u + 4*d₁*d₂^3*u + d₂^4 := by
    positivity
  have hid : cyc2N d₁ d₂ u 1
      = 9*d₁^3*d₂ * (u * (u - 1)^2) + 4*d₁^3*d₂*u^2
        + (d₁^4*u^2 + 4*d₁^2*d₂^2*u^2 + 2*d₁^2*d₂^2*u + 4*d₁*d₂^3*u + d₂^4) := by
    unfold cyc2N; ring
  have h4 : (0:ℝ) ≤ 4*d₁^3*d₂*u^2 := by positivity
  rw [hid]; linarith

/-- **The `v = 0` endpoint** is the acyclic case: `cyc2N d₁ d₂ u 0` is `coxE` at holding means
`t₁ = 1/d₂`, `t₂ = 1/d₁` and continuation probability `u`, cleared of denominators.  Concretely it
is the same quadratic-in-`u` shape, and nonnegativity follows exactly as in `coxE_nonneg`. -/
theorem cyc2N_at_zero_nonneg (d₁ d₂ u : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ cyc2N d₁ d₂ u 0 := by
  -- `cyc2N _ _ u 0 = u²·d₁²·(d₁² − 7d₁d₂ + d₂²) + u·d₁d₂·(9d₁² − 7d₁d₂ + 2d₂²) + d₂⁴`
  -- (in the variables `d`), the same shape as `coxE` with the roles of the rates swapped.
  have hid : cyc2N d₁ d₂ u 0
      = u^2 * d₁^2 * (d₁^2 - 7*d₁*d₂ + d₂^2)
        + u * (d₁*d₂ * (9*d₁^2 - 7*d₁*d₂ + 2*d₂^2)) + d₂^4 := by
    unfold cyc2N; ring
  rw [hid]
  rcases le_or_gt 0 (d₁^2 - 7*d₁*d₂ + d₂^2) with hq | hq
  · have hlin : 0 < 9*d₁^2 - 7*d₁*d₂ + 2*d₂^2 := by
      nlinarith [sq_nonneg (3*d₁ - d₂), sq_nonneg d₁, sq_nonneg d₂, mul_pos hd₁ hd₂]
    have h1 : 0 ≤ u^2 * d₁^2 * (d₁^2 - 7*d₁*d₂ + d₂^2) := by positivity
    have h2 : 0 ≤ u * (d₁*d₂ * (9*d₁^2 - 7*d₁*d₂ + 2*d₂^2)) :=
      mul_nonneg hu0 (mul_nonneg (by positivity) (le_of_lt hlin))
    have h3 : (0:ℝ) ≤ d₂^4 := by positivity
    linarith
  · -- concave in u: reuse the endpoint lemma with a = d₁²(d₁²−7d₁d₂+d₂²) ≤ 0
    have hA : d₁^2 * (d₁^2 - 7*d₁*d₂ + d₂^2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_lt hq)
    have hc : (0:ℝ) ≤ d₂^4 := by positivity
    have hsum : 0 ≤ d₁^2 * (d₁^2 - 7*d₁*d₂ + d₂^2)
        + d₁*d₂ * (9*d₁^2 - 7*d₁*d₂ + 2*d₂^2) + d₂^4 := by
      nlinarith [sq_nonneg (d₁ - d₂), mul_pos hd₁ hd₂, sq_nonneg (d₁ + d₂),
        mul_nonneg (mul_nonneg (le_of_lt hd₁) (le_of_lt hd₂)) (sq_nonneg (d₁ - d₂)),
        mul_nonneg (mul_nonneg (le_of_lt hd₁) (le_of_lt hd₁)) (sq_nonneg (d₁ - d₂)),
        mul_nonneg (mul_nonneg (le_of_lt hd₂) (le_of_lt hd₂)) (sq_nonneg (d₁ - d₂))]
    have := concave_quad_ge_endpoints (d₁^2 * (d₁^2 - 7*d₁*d₂ + d₂^2))
      (d₁*d₂ * (9*d₁^2 - 7*d₁*d₂ + 2*d₂^2)) (d₂^4) u hA hu0 hu1 hc hsum
    nlinarith [this]

/-- **Theorem (order two with a cycle).**  For all exit rates `d₁,d₂ > 0` and routing
probabilities `u,v ∈ [0,1]`, the numerator of `9a₁a₃ − 8a₂²` for the order-two two-cycle is
nonnegative.  Hence `a₁a₃/a₂² ≥ 8/9 = κ₂` for *every* order-two phase-type law, cyclic or not.

The proof is the `v`-dichotomy: `cyc2N` is concave in `v` (leading coefficient `−8d₁²d₂²u²`), so
its minimum over `[0,1]` is at an endpoint, and both endpoints are nonnegative --- `v = 0` being
the acyclic case and `v = 1` following from `u(u−1)² ≥ 0`. -/
theorem cyc2N_nonneg (d₁ d₂ u v : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ cyc2N d₁ d₂ u v := by
  set a : ℝ := -(8*d₁^2*d₂^2*u^2) with ha
  set b : ℝ := d₁*d₂*u * (9*d₁^2*u^2 - 7*d₁^2*u + 11*d₁*d₂*u + 9*d₁*d₂ + 2*d₂^2) with hb
  set c : ℝ := cyc2N d₁ d₂ u 0 with hc
  have hE : cyc2N d₁ d₂ u v = a * v^2 + b * v + c := cyc2N_quad d₁ d₂ u v
  have hane : a ≤ 0 := by rw [ha]; nlinarith [sq_nonneg (d₁*d₂*u)]
  have h0 : 0 ≤ c := cyc2N_at_zero_nonneg d₁ d₂ u hd₁ hd₂ hu0 hu1
  have h1 : 0 ≤ a + b + c := by
    have := cyc2N_at_one_nonneg d₁ d₂ u hd₁ hd₂ hu0
    have heq : cyc2N d₁ d₂ u 1 = a + b + c := by
      have := cyc2N_quad d₁ d₂ u 1; rw [this]; ring
    linarith [heq ▸ this]
  rw [hE]
  exact concave_quad_ge_endpoints a b c v hane hv0 hv1 h0 h1

/-! ## Order three with a two-cycle, started inside the cycle

Take the order-three routing `p₁₂ = u`, `p₂₁ = v`, `p₃₂ = w`: a two-cycle on `{1,2}` fed by the
third state.  Started at state `1`, the numerator of `12a₁a₃ − 10a₂²` is **concave** in the
back-edge `v` (leading coefficient `−10d₁²d₂²u²`), so the `s = 2` argument extends: the minimum
over `v ∈ [0,1]` is at an endpoint, and both endpoints are nonnegative.  Note that from state `1`
with `v = 0` the walk never reaches state `3`, so that endpoint is an order-two law. -/

/-- The numerator of `12a₁a₃ − 10a₂²` at the `v = 1` endpoint, started at state `1`
(divided by the positive constant `2`). -/
noncomputable def cyc3N1 (d₁ d₂ u : ℝ) : ℝ :=
  d₁^4*u^2 + 6*d₁^3*d₂*u^3 - 8*d₁^3*d₂*u^2 + 6*d₁^3*d₂*u + 4*d₁^2*d₂^2*u^2
    + 2*d₁^2*d₂^2*u + 4*d₁*d₂^3*u + d₂^4

/-- The `v = 1` endpoint is nonnegative: the only negative term `−8d₁³d₂u²` is absorbed by
`6d₁³d₂·u(u−1)² ≥ 0`, leaving a sum of nonnegative monomials. -/
theorem cyc3N1_nonneg (d₁ d₂ u : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hu : 0 ≤ u) :
    0 ≤ cyc3N1 d₁ d₂ u := by
  have hid : cyc3N1 d₁ d₂ u
      = 6*d₁^3*d₂ * (u * (u - 1)^2)
        + (d₁^4*u^2 + 4*d₁^3*d₂*u^2 + 4*d₁^2*d₂^2*u^2 + 2*d₁^2*d₂^2*u
            + 4*d₁*d₂^3*u + d₂^4) := by
    unfold cyc3N1; ring
  rw [hid]; positivity

/-- The `u = 1` value of the `v = 0` endpoint, nonnegative via
`2d₁d₂(d₁−d₂)² + d₁⁴ + d₁²d₂² + d₂⁴`. -/
theorem cyc3N0_at_one_nonneg (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    0 ≤ d₁^4 + 2*d₁^3*d₂ - 3*d₁^2*d₂^2 + 2*d₁*d₂^3 + d₂^4 := by
  have hid : d₁^4 + 2*d₁^3*d₂ - 3*d₁^2*d₂^2 + 2*d₁*d₂^3 + d₂^4
      = 2*d₁*d₂*(d₁ - d₂)^2 + (d₁^4 + d₁^2*d₂^2 + d₂^4) := by ring
  rw [hid]; positivity

/-- **The `v = 0` endpoint**, an order-two law measured against the order-three constant:
`u²d₁²(d₁²−4d₁d₂+d₂²) + u·d₁d₂(6d₁²−4d₁d₂+2d₂²) + d₂⁴ ≥ 0`.  The linear coefficient is positive
(`6X²−4X+2` has discriminant `16−48<0`) and the dichotomy in `u` closes it. -/
theorem cyc3N0_nonneg (d₁ d₂ u : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ u^2 * (d₁^2*(d₁^2 - 4*d₁*d₂ + d₂^2))
        + u * (d₁*d₂*(6*d₁^2 - 4*d₁*d₂ + 2*d₂^2)) + d₂^4 := by
  have hlin : 0 < 6*d₁^2 - 4*d₁*d₂ + 2*d₂^2 := by
    nlinarith [sq_nonneg (d₁ - d₂), sq_nonneg d₁, sq_nonneg d₂]
  rcases le_or_gt 0 (d₁^2 - 4*d₁*d₂ + d₂^2) with hq | hq
  · have h1 : 0 ≤ u^2 * (d₁^2*(d₁^2 - 4*d₁*d₂ + d₂^2)) := by
      apply mul_nonneg (sq_nonneg u)
      exact mul_nonneg (by positivity) hq
    have h2 : 0 ≤ u * (d₁*d₂*(6*d₁^2 - 4*d₁*d₂ + 2*d₂^2)) :=
      mul_nonneg hu0 (mul_nonneg (by positivity) (le_of_lt hlin))
    have h3 : (0:ℝ) ≤ d₂^4 := by positivity
    linarith
  · have hA : d₁^2*(d₁^2 - 4*d₁*d₂ + d₂^2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_lt hq)
    have hc : (0:ℝ) ≤ d₂^4 := by positivity
    have hsum : 0 ≤ d₁^2*(d₁^2 - 4*d₁*d₂ + d₂^2) + d₁*d₂*(6*d₁^2 - 4*d₁*d₂ + 2*d₂^2) + d₂^4 := by
      have := cyc3N0_at_one_nonneg d₁ d₂ hd₁ hd₂
      nlinarith [this]
    have h := concave_quad_ge_endpoints (d₁^2*(d₁^2 - 4*d₁*d₂ + d₂^2))
      (d₁*d₂*(6*d₁^2 - 4*d₁*d₂ + 2*d₂^2)) (d₂^4) u hA hu0 hu1 hc hsum
    linarith [h]

/-! ## The start-state-2 reduction at order three

For the cyclic pattern `p₁₂ = u`, `p₂₁ = v`, `p₃₂ = w` started at state `2`, the numerator of
`12a₁a₃ − 10a₂²` is cubic in `v` with positive leading coefficient, and its `v`-derivative equals
`4d₂·G`.  Scaling by `d₂³` and putting `p = d₁/d₂`, `G` becomes `Av² + Bv + C` with

  `A = 9pu`,  `B = −5p²u² + 8p²u + p² − 4pu − 4p + 1`,
  `C = p(p²u + p² + 3pu − 2p + 3)`.

Two facts are unconditional: `A ≥ 0`, so the form is convex in `v`, and `C > 0`.  Hence `G ≥ 0`
on `v ∈ [0,1]` reduces to the vertex estimate `4AC ≥ B²` on the region `−2A ≤ B ≤ 0`. -/

/-- `A = 9pu ≥ 0`: the scaled `G` is convex in `v`. -/
theorem Gscaled_A_nonneg (p u : ℝ) (hp : 0 ≤ p) (hu : 0 ≤ u) : 0 ≤ 9*p*u := by positivity

/-- **`C > 0`.**  The bracket `p²u + p² + 3pu − 2p + 3` is a quadratic in `p` with positive
leading coefficient `u+1` and discriminant `(3u−2)² − 12(u+1) = 9u² − 24u − 8`, which is negative
for `u ∈ [0,1]` (it is `−8` at `u = 0` and `−23` at `u = 1`).  Formalization shows `u ≤ 1` is
not in fact needed: `C > 0` for every `u ≥ 0`. -/
theorem Gscaled_C_pos (p u : ℝ) (hp : 0 < p) (hu0 : 0 ≤ u) :
    0 < p * (p^2*u + p^2 + 3*p*u - 2*p + 3) := by
  have hbr : 0 < p^2*u + p^2 + 3*p*u - 2*p + 3 := by
    nlinarith [sq_nonneg (p - 1), sq_nonneg p, mul_nonneg hu0 (sq_nonneg p),
      mul_nonneg hu0 hp.le, sq_nonneg (p*u), mul_nonneg (mul_nonneg hu0 hp.le) hp.le]
  exact mul_pos hp hbr

/-- **The reduction.**  A convex quadratic `Av² + Bv + C` with `A ≥ 0` and `C ≥ 0` is nonnegative
on `[0,1]` provided that, whenever its vertex is admissible (`−2A ≤ B ≤ 0`), the vertex value is
nonnegative (`B² ≤ 4AC`).  This is the step that reduces `G ≥ 0` to the vertex estimate. -/
theorem convex_quad_nonneg_on_unit (A B C v : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hend : 0 ≤ A + B + C)
    (hvertex : -2*A ≤ B → B ≤ 0 → B^2 ≤ 4*A*C) :
    0 ≤ A * v^2 + B * v + C := by
  rcases le_or_gt 0 B with hb | hb
  · -- B ≥ 0: every term is nonnegative
    have : 0 ≤ B * v := mul_nonneg hb hv0
    have : 0 ≤ A * v^2 := mul_nonneg hA (sq_nonneg v)
    linarith [mul_nonneg hA (sq_nonneg v), mul_nonneg hb hv0]
  · rcases le_or_gt (-2*A) B with hin | hout
    · -- vertex admissible: use `4AC ≥ B²`, i.e. the value at the vertex is ≥ 0
      have hb2 := hvertex hin (le_of_lt hb)
      rcases eq_or_lt_of_le hA with hA0 | hApos
      · -- A = 0: then B² ≤ 0 so B = 0, contradicting B < 0
        exfalso
        rw [← hA0] at hb2
        nlinarith [sq_nonneg B]
      · -- A > 0: complete the square
        have key : A * (A * v^2 + B * v + C) = (A*v + B/2)^2 + (4*A*C - B^2)/4 := by
          field_simp; ring
        nlinarith [sq_nonneg (A*v + B/2), hb2, hApos, key]
    · -- vertex to the right of 1: the quadratic is decreasing on [0,1], min at v = 1
      have hmono : A * v^2 + B * v + C ≥ A + B + C - (1 - v) * (A * (1 + v) + B) := by
        nlinarith [sq_nonneg v]
      have hfac : A * (1 + v) + B ≤ 0 := by nlinarith [hv1, hA, hout]
      have hfv : (0:ℝ) ≤ (1 - v) * (-(A * (1 + v) + B)) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hend, hfv]

/-- **`2C + B > 0` unconditionally** for `p ≥ 0`, `u ∈ [0,1]`.  This is the key estimate:
`2C + B = 2p³u + 2p³ − 5p²u² + 14p²u − 3p² − 4pu + 2p + 1`, whose minimum over the region is
about `0.848`, attained near `p ≈ 0.145`, `u = 1`. -/
theorem twoC_plus_B_pos (p u : ℝ) (hp : 0 ≤ p) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 < 2*p^3*u + 2*p^3 - 5*p^2*u^2 + 14*p^2*u - 3*p^2 - 4*p*u + 2*p + 1 := by
  nlinarith [sq_nonneg (p - 1), sq_nonneg p, sq_nonneg (2*p - 1), sq_nonneg (3*p - 1),
    mul_nonneg hp hu0, mul_nonneg (mul_nonneg hp hp) hu0,
    mul_nonneg (mul_nonneg (mul_nonneg hp hp) hp) hu0,
    mul_nonneg hu0 (sub_nonneg.mpr hu1),
    mul_nonneg (mul_nonneg hp hp) (mul_nonneg hu0 (sub_nonneg.mpr hu1)),
    mul_nonneg hp (sq_nonneg (p - 1)), mul_nonneg hu0 (sq_nonneg (p - 1)),
    mul_nonneg (mul_nonneg hp hu0) (sub_nonneg.mpr hu1), sq_nonneg (p*u - p)]

/-- **The vertex estimate (`conj:vertexest`), PROVED.**  On the region `−2A ≤ B ≤ 0` we have
`−B ≤ 2A`, hence `B² = (−B)(−B) ≤ 2A(−B)`, so
`4AC − B² ≥ 4AC − 2A(−B) = 2A(2C + B) ≥ 0` by `twoC_plus_B_pos`. -/
theorem vertex_estimate (p u : ℝ) (hp : 0 < p) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hlo : -2*(9*p*u) ≤ (-5*p^2*u^2 + 8*p^2*u + p^2 - 4*p*u - 4*p + 1))
    (hhi : (-5*p^2*u^2 + 8*p^2*u + p^2 - 4*p*u - 4*p + 1) ≤ 0) :
    (-5*p^2*u^2 + 8*p^2*u + p^2 - 4*p*u - 4*p + 1)^2
      ≤ 4*(9*p*u)*(p*(p^2*u + p^2 + 3*p*u - 2*p + 3)) := by
  set A : ℝ := 9*p*u with hA
  set B : ℝ := -5*p^2*u^2 + 8*p^2*u + p^2 - 4*p*u - 4*p + 1 with hB
  set C : ℝ := p*(p^2*u + p^2 + 3*p*u - 2*p + 3) with hC
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  -- B² ≤ 2A(−B), because 0 ≤ −B ≤ 2A
  have hnB : 0 ≤ -B := by linarith
  have hnB2 : -B ≤ 2*A := by linarith
  have hsq : B^2 ≤ 2*A*(-B) := by nlinarith [hnB, hnB2]
  -- 2C + B > 0
  have hkey : 0 < 2*C + B := by
    rw [hC, hB]
    have := twoC_plus_B_pos p u (le_of_lt hp) hu0 hu1
    nlinarith [this]
  -- assemble
  nlinarith [hsq, mul_nonneg hAnn (le_of_lt hkey), hAnn, hkey]

/-! ## Start state three: the `v = 0` endpoint

For the feeder state (start `3`) the numerator is quartic in `v`, and at `v = 0` it factors as
`2d₁⁴` times exactly the expression already handled at the `v = 0` endpoint of start `1`, with
`(d₃,d₂,w)` in place of `(d₁,d₂,u)` — note the two rates swap roles.  So that endpoint is free. -/

/-- **The `v = 0` endpoint for start state 3.**  The bracket is the `cyc3N0` expression in
`(d₃,d₂,w)`, so `cyc3N0_nonneg` applies after swapping the two rates. -/
theorem cyc3_start3_at_zero_nonneg (d₁ d₂ d₃ w : ℝ) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    0 ≤ 2*d₁^4 * (d₂^4 + 2*d₂^3*d₃*w + d₂^2*d₃^2*w^2 - 4*d₂^2*d₃^2*w
        - 4*d₂*d₃^3*w^2 + 6*d₂*d₃^3*w + d₃^4*w^2) := by
  -- the correspondence swaps the roles of the two rates: `(d₁,d₂,u) ↦ (d₃,d₂,w)`
  have hbr := cyc3N0_nonneg d₃ d₂ w hd₃ hd₂ hw0 hw1
  have hid : d₂^4 + 2*d₂^3*d₃*w + d₂^2*d₃^2*w^2 - 4*d₂^2*d₃^2*w
        - 4*d₂*d₃^3*w^2 + 6*d₂*d₃^3*w + d₃^4*w^2
      = w^2 * (d₃^2*(d₃^2 - 4*d₃*d₂ + d₂^2))
        + w * (d₃*d₂*(6*d₃^2 - 4*d₃*d₂ + 2*d₂^2)) + d₂^4 := by ring
  have h4 : (0:ℝ) ≤ 2*d₁^4 := by positivity
  rw [hid]
  exact mul_nonneg h4 hbr

/-! ## The general acyclic (upper triangular) case

For an upper triangular substochastic `A` the transient chain visits each state at most once, so
conditioning on the realised path expresses the moments as a *finite convex combination* of chain
moments:
`aₖ = ∑_{paths} w_path · hₖ(c_path)` with `w_path ≥ 0`, `∑ w_path = 1`, where `c_path` lists the
reciprocal exit rates of the visited states.  (We verified this identity symbolically for
`s ≤ 3` and all starting states.)

Given that decomposition, the bound follows from two facts already established here: the chain
inequality `3(s+1)h₁h₃ ≥ 2(s+2)h₂²` of `chain_ineq` applied to each path, and closure of the bound
under convex combinations.  The second is what we formalize: a Cauchy–Schwarz argument showing that
if every component of a mixture satisfies `κ·y² ≤ x·z`, so does the mixture. -/

/-- **Mixture closure.**  If `κ·yⱼ² ≤ xⱼzⱼ` for every `j`, with `xⱼ, zⱼ ≥ 0` and `κ ≥ 0`, then the
same holds for any convex combination: `κ·(∑wⱼyⱼ)² ≤ (∑wⱼxⱼ)(∑wⱼzⱼ)`.

This is the two-step argument of the classical mixture lemma: Cauchy–Schwarz for the weighted sums
gives `(∑wⱼ√(xⱼzⱼ))² ≤ (∑wⱼxⱼ)(∑wⱼzⱼ)`, and `√(xⱼzⱼ) ≥ √κ·yⱼ` termwise. -/
theorem mixture_closure_sq (t : Finset ι) (w x y z : ι → ℝ) (κ : ℝ)
    (hκ : 0 ≤ κ) (hw : ∀ j ∈ t, 0 ≤ w j)
    (hx : ∀ j ∈ t, 0 ≤ x j) (hz : ∀ j ∈ t, 0 ≤ z j)
    (hy : ∀ j ∈ t, 0 ≤ y j)
    (hcomp : ∀ j ∈ t, κ * (y j)^2 ≤ x j * z j) :
    κ * (∑ j ∈ t, w j * y j)^2
      ≤ (∑ j ∈ t, w j * x j) * (∑ j ∈ t, w j * z j) := by
  classical
  -- Cauchy–Schwarz on the vectors `√(wⱼxⱼ)` and `√(wⱼzⱼ)`
  set U : ι → ℝ := fun j => Real.sqrt (w j * x j) with hU
  set V : ι → ℝ := fun j => Real.sqrt (w j * z j) with hV
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq t U V
  have eU : ∑ j ∈ t, (U j)^2 = ∑ j ∈ t, w j * x j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    exact Real.sq_sqrt (mul_nonneg (hw j hj) (hx j hj))
  have eV : ∑ j ∈ t, (V j)^2 = ∑ j ∈ t, w j * z j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    exact Real.sq_sqrt (mul_nonneg (hw j hj) (hz j hj))
  -- termwise: `√κ · wⱼyⱼ ≤ UⱼVⱼ`
  have hterm : ∀ j ∈ t, Real.sqrt κ * (w j * y j) ≤ U j * V j := by
    intro j hj
    have hwj := hw j hj
    have hyj := hy j hj
    have h1 : U j * V j = Real.sqrt ((w j)^2 * (x j * z j)) := by
      rw [hU, hV, ← Real.sqrt_mul (mul_nonneg hwj (hx j hj))]
      congr 1; ring
    have hsq : Real.sqrt κ * (w j * y j) = Real.sqrt (κ * ((w j)^2 * (y j)^2)) := by
      rw [Real.sqrt_mul hκ, Real.sqrt_mul (sq_nonneg (w j)), Real.sqrt_sq hwj,
        Real.sqrt_sq hyj]
    rw [h1, hsq]
    apply Real.sqrt_le_sqrt
    have := hcomp j hj
    nlinarith [sq_nonneg (w j), this]
  -- assemble
  have hsum : Real.sqrt κ * (∑ j ∈ t, w j * y j) ≤ ∑ j ∈ t, U j * V j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hnn : 0 ≤ Real.sqrt κ * (∑ j ∈ t, w j * y j) := by
    apply mul_nonneg (Real.sqrt_nonneg κ)
    exact Finset.sum_nonneg fun j hj => mul_nonneg (hw j hj) (hy j hj)
  have hkey : (Real.sqrt κ * (∑ j ∈ t, w j * y j))^2 ≤ (∑ j ∈ t, U j * V j)^2 := by
    apply sq_le_sq' (by linarith) hsum
  have hexp : (Real.sqrt κ * (∑ j ∈ t, w j * y j))^2 = κ * (∑ j ∈ t, w j * y j)^2 := by
    rw [mul_pow, Real.sq_sqrt hκ]
  rw [← eU, ← eV]
  calc κ * (∑ j ∈ t, w j * y j)^2
      = (Real.sqrt κ * (∑ j ∈ t, w j * y j))^2 := hexp.symm
    _ ≤ (∑ j ∈ t, U j * V j)^2 := hkey
    _ ≤ (∑ j ∈ t, (U j)^2) * (∑ j ∈ t, (V j)^2) := hcs

/-- **The general acyclic case, `k = 2`.**  Suppose the moments of an order-`s` law admit the
path decomposition
`aⱼ = ∑_{paths} w_path · Hⱼ(path)` for `j = 1,2,3`,
with nonnegative weights, and suppose each path's triple satisfies the chain inequality
`2(s+2)·H₂² ≤ 3(s+1)·H₁H₃` (which is `chain_ineq` for a hypoexponential).  Then the mixture
satisfies the same bound:
`2(s+2)·a₂² ≤ 3(s+1)·a₁a₃`, i.e. `a₁a₃/a₂² ≥ κ_s = 2(s+2)/(3(s+1))`.

This is the algebraic content of the triangular theorem at `k = 2`: upper triangularity supplies
the decomposition (each state is visited at most once, so conditioning on the path gives a
hypoexponential), and this lemma supplies the closure. -/
theorem acyclic_k2_of_decomposition (t : Finset ι) (w H₁ H₂ H₃ : ι → ℝ) (n : ℝ)
    (hn : 0 ≤ n) (hw : ∀ j ∈ t, 0 ≤ w j)
    (h1 : ∀ j ∈ t, 0 ≤ H₁ j) (h2 : ∀ j ∈ t, 0 ≤ H₂ j) (h3 : ∀ j ∈ t, 0 ≤ H₃ j)
    (hchain : ∀ j ∈ t, 2*(n + 2) * (H₂ j)^2 ≤ 3*(n + 1) * (H₁ j * H₃ j)) :
    2*(n + 2) * (∑ j ∈ t, w j * H₂ j)^2
      ≤ 3*(n + 1) * ((∑ j ∈ t, w j * H₁ j) * (∑ j ∈ t, w j * H₃ j)) := by
  -- normalise to `κ = 2(n+2)/(3(n+1))` and apply the mixture closure
  have h3n : (0:ℝ) < 3*(n + 1) := by linarith
  set κ : ℝ := 2*(n + 2) / (3*(n + 1)) with hκdef
  have hκ : 0 ≤ κ := by rw [hκdef]; positivity
  have hcomp : ∀ j ∈ t, κ * (H₂ j)^2 ≤ H₁ j * H₃ j := by
    intro j hj
    rw [hκdef, div_mul_eq_mul_div, div_le_iff₀ h3n]
    nlinarith [hchain j hj]
  have hmix := mixture_closure_sq t w H₁ H₂ H₃ κ hκ hw h1 h3 h2 hcomp
  rw [hκdef, div_mul_eq_mul_div, div_le_iff₀ h3n] at hmix
  nlinarith [hmix]

/-! ## The acyclic case for general `k`

For general `k` the content is that the normalised moments `Bₖ = k!·hₖ(c)/(s)ₖ` form a Stieltjes
moment sequence.  The mechanism: `Dirichlet(1,…,1)` is exactly the *uniform* measure on the standard
simplex, so with `Y = ⟨c, X⟩` for `X` uniform on the simplex,

  `Bₖ = E[Yᵏ]`,

and `Bₖ² ≤ B_{k−1}B_{k+1}` is Cauchy–Schwarz applied to `Y^{(k−1)/2}` and `Y^{(k+1)/2}`.  Unwinding
the constants, the per-path inequality needed is
`k(s+k)·hₖ² ≤ (k+1)(s+k−1)·h_{k−1}h_{k+1}`.

We formalize the piece that is an inequality: the moment step (`moment_cs_step`), Cauchy–Schwarz
between `y^{k}` and `y^{k+2}` for a nonnegative weight.  The identity `Bₖ = E[Yᵏ]` is a computation
about the uniform measure on the simplex, not an inequality, and is not formalized here. -/

/-- **The abstract moment step.**  If `Mₖ = ∫ yᵏ dμ` for a nonnegative measure and `y ≥ 0`, then
`Mₖ² ≤ M_{k−1}M_{k+1}`.  Stated here in the finite form we need: for nonnegative weights `ν` on a
finite index set and nonnegative `y`, the Cauchy–Schwarz inequality between `y^{k−1}` and `y^{k+1}`.

This is the discrete shadow of the Stieltjes step; combined with the identity `Bₖ = E[Yᵏ]` it gives
log-convexity for every `k`. -/
theorem moment_cs_step (t : Finset ι) (ν y : ι → ℝ) (k : ℕ)
    (hν : ∀ j ∈ t, 0 ≤ ν j) (hy : ∀ j ∈ t, 0 ≤ y j) :
    (∑ j ∈ t, ν j * (y j)^(k+1))^2
      ≤ (∑ j ∈ t, ν j * (y j)^k) * (∑ j ∈ t, ν j * (y j)^(k+2)) := by
  classical
  set U : ι → ℝ := fun j => Real.sqrt (ν j * (y j)^k) with hU
  set V : ι → ℝ := fun j => Real.sqrt (ν j * (y j)^(k+2)) with hV
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq t U V
  have eU : ∑ j ∈ t, (U j)^2 = ∑ j ∈ t, ν j * (y j)^k := by
    refine Finset.sum_congr rfl fun j hj => ?_
    exact Real.sq_sqrt (mul_nonneg (hν j hj) (pow_nonneg (hy j hj) k))
  have eV : ∑ j ∈ t, (V j)^2 = ∑ j ∈ t, ν j * (y j)^(k+2) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    exact Real.sq_sqrt (mul_nonneg (hν j hj) (pow_nonneg (hy j hj) (k+2)))
  have eUV : ∑ j ∈ t, U j * V j = ∑ j ∈ t, ν j * (y j)^(k+1) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have h0 : 0 ≤ ν j * (y j)^k := mul_nonneg (hν j hj) (pow_nonneg (hy j hj) k)
    have hyj := hy j hj
    have hprod : ν j * (y j)^k * (ν j * (y j)^(k+2)) = (ν j * (y j)^(k+1))^2 := by ring
    change Real.sqrt (ν j * (y j)^k) * Real.sqrt (ν j * (y j)^(k+2)) = _
    rw [← Real.sqrt_mul h0, hprod,
      Real.sqrt_sq (mul_nonneg (hν j hj) (pow_nonneg hyj (k+1)))]
  rw [← eU, ← eV, ← eUV]
  exact hcs

/-- **The general-`k` acyclic bound, from the path decomposition.**  Suppose that for each path
`j` the normalised moments satisfy `Bₖ(j)² ≤ B_{k−1}(j)·B_{k+1}(j)` --- which the moment step
supplies, `Bₖ(j)` being the `k`-th moment of `⟨c_j, X⟩` for `X` uniform on the simplex --- and let
`w` be nonnegative weights.  Then the mixture satisfies the same bound.

Combined with the identity `Bₖ = k!·hₖ(c)/(s)ₖ`, this is the triangular theorem at every `k`:
the acyclic structure gives the decomposition, `moment_cs_step` gives each component, and this
lemma closes it under mixing. -/
theorem acyclic_general_k_of_decomposition (t : Finset ι) (w B₀ B₁ B₂ : ι → ℝ)
    (hw : ∀ j ∈ t, 0 ≤ w j)
    (h0 : ∀ j ∈ t, 0 ≤ B₀ j) (h1 : ∀ j ∈ t, 0 ≤ B₁ j) (h2 : ∀ j ∈ t, 0 ≤ B₂ j)
    (hcomp : ∀ j ∈ t, (B₁ j)^2 ≤ B₀ j * B₂ j) :
    (∑ j ∈ t, w j * B₁ j)^2
      ≤ (∑ j ∈ t, w j * B₀ j) * (∑ j ∈ t, w j * B₂ j) := by
  have := mixture_closure_sq t w B₀ B₁ B₂ 1 zero_le_one hw h0 h2 h1
    (by intro j hj; simpa using hcomp j hj)
  simpa using this

/-- **Rescaling a log-convexity inequality.**  If `Bₖ = rₖ·hₖ`, then `B₁² ≤ B₀B₂`
is exactly `r₁²·h₁² ≤ r₀r₂·h₀h₂`
(no positivity needed — it is a rearrangement).
This is the bookkeeping step turning the normalised moment inequality into the `hₖ` form. -/
theorem logconvex_rescale (r₀ r₁ r₂ h₀ h₁ h₂ : ℝ)
    (hB : (r₁ * h₁)^2 ≤ (r₀ * h₀) * (r₂ * h₂)) :
    r₁^2 * h₁^2 ≤ (r₀ * r₂) * (h₀ * h₂) := by
  nlinarith [hB]

/-- **The `hₖ` form, with the factorial constants unwound.**  Taking
`r_{k-1} = (k-1)!/(n)_{k-1}`, `r_k = k!/(n)_k`, `r_{k+1} = (k+1)!/(n)_{k+1}` in
`logconvex_rescale` and clearing, the normalised inequality `Bₖ² ≤ B_{k−1}B_{k+1}` becomes

  `k(n+k)·hₖ² ≤ (k+1)(n+k−1)·h_{k−1}h_{k+1}`,

because `(k!)²/((k−1)!(k+1)!) = k/(k+1)` and `(n)ₖ²/((n)_{k−1}(n)_{k+1}) = (n+k−1)/(n+k)`.

We state the resulting arithmetic step: from the inequality in the form
`(k/(k+1))·h₁² ≤ ((n+k−1)/(n+k))·h₀h₂` one obtains the polynomial form. -/
theorem hk_form_of_ratio (n kk h₀ h₁ h₂ : ℝ) (hn : 0 < n) (hkk : 0 < kk)
    (hratio : (kk / (kk + 1)) * h₁^2 ≤ ((n + kk - 1) / (n + kk)) * (h₀ * h₂)) :
    (kk * (n + kk)) * h₁^2 ≤ ((kk + 1) * (n + kk - 1)) * (h₀ * h₂) := by
  have hk1 : (0:ℝ) < kk + 1 := by linarith
  have hnk : (0:ℝ) < n + kk := by linarith
  -- clear both denominators by multiplying through
  have h1 : (kk / (kk + 1)) * h₁^2 * ((kk + 1) * (n + kk))
      = (kk * (n + kk)) * h₁^2 := by field_simp
  have h2 : ((n + kk - 1) / (n + kk)) * (h₀ * h₂) * ((kk + 1) * (n + kk))
      = ((kk + 1) * (n + kk - 1)) * (h₀ * h₂) := by field_simp
  have hpos : (0:ℝ) < (kk + 1) * (n + kk) := mul_pos hk1 hnk
  have := mul_le_mul_of_nonneg_right hratio (le_of_lt hpos)
  rw [h1, h2] at this
  exact this

/-! ## Start state three, the `v = 1` endpoint

Normalising `d₂ = 1`, the `v = 1` endpoint of the start-3 numerator is a quadratic in the remaining
routing probability `w`: `A₂w² + A₁w + A₀` with
`A₀ = 2d₁⁴(u−1)⁴` and `A₁ = −4d₁d₃(u−1)·Φ`.  Since `u ≤ 1` the prefactor of `Φ` is nonnegative, and
`Φ`'s leading coefficient in `d₁` is a manifest sum of squares.  `A₂` is sign-indefinite, so the
argument splits on its sign; the `A₂ < 0` branch reduces to `w ∈ {0,1}`, and the `w = 1` value
`A₂+A₁+A₀` is the one piece not yet certified. -/

/-- `A₀ = 2d₁⁴(u−1)⁴ ≥ 0`. -/
theorem start3_A0_nonneg (d₁ u : ℝ) : 0 ≤ 2*d₁^4*(u - 1)^4 := by positivity

/-- The `d₁³` coefficient of `Φ` is a sum of squares: `3d₃² + 2d₃(u−1) + (u−1)² =
(u−1+d₃)² + 2d₃²`. -/
theorem start3_Phi_lead (d₃ u : ℝ) :
    3*d₃^2 + 2*d₃*(u - 1) + (u - 1)^2 = (u - 1 + d₃)^2 + 2*d₃^2 := by ring

/-- **The prefactor of `Φ` in `A₁` is nonnegative** when `u ≤ 1`: `−4d₁d₃(u−1) ≥ 0`. -/
theorem start3_A1_prefactor_nonneg (d₁ d₃ u : ℝ) (hd₁ : 0 ≤ d₁) (hd₃ : 0 ≤ d₃)
    (hu : u ≤ 1) : 0 ≤ -4*d₁*d₃*(u - 1) := by
  have h : 0 ≤ 1 - u := by linarith
  nlinarith [mul_nonneg (mul_nonneg hd₁ hd₃) h]

/-- **The `A₂ ≥ 0` branch.**  If all three coefficients are nonnegative then the quadratic is
nonnegative for `w ≥ 0` — this is `quad_nonneg_of_coeffs` specialised to the start-3 endpoint. -/
theorem start3_endpoint_of_A2_nonneg (A₂ A₁ A₀ w : ℝ)
    (h₂ : 0 ≤ A₂) (h₁ : 0 ≤ A₁) (h₀ : 0 ≤ A₀) (hw : 0 ≤ w) :
    0 ≤ A₂ * w^2 + A₁ * w + A₀ :=
  quad_nonneg_of_coeffs A₂ A₁ A₀ w h₂ h₁ h₀ hw

/-- **The `A₂ < 0` branch.**  A concave quadratic on `[0,1]` is bounded below by its endpoint
values `A₀` and `A₂+A₁+A₀` — this is `concave_quad_ge_endpoints` specialised. -/
theorem start3_endpoint_of_A2_neg (A₂ A₁ A₀ w : ℝ)
    (h₂ : A₂ ≤ 0) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (h₀ : 0 ≤ A₀) (h₁ : 0 ≤ A₂ + A₁ + A₀) :
    0 ≤ A₂ * w^2 + A₁ * w + A₀ :=
  concave_quad_ge_endpoints A₂ A₁ A₀ w h₂ hw0 hw1 h₀ h₁

/-- **The start-3 `v = 1` endpoint, modulo the `w = 1` value.**  Combining the two branches: the
endpoint is nonnegative given `A₀ ≥ 0`, `A₁ ≥ 0`, and (only when `A₂ < 0`) `A₂+A₁+A₀ ≥ 0`. -/
theorem start3_endpoint_nonneg (A₂ A₁ A₀ w : ℝ)
    (h₀ : 0 ≤ A₀) (h₁ : 0 ≤ A₁) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hsum : 0 ≤ A₂ + A₁ + A₀) :
    0 ≤ A₂ * w^2 + A₁ * w + A₀ := by
  rcases le_or_gt 0 A₂ with h | h
  · exact start3_endpoint_of_A2_nonneg A₂ A₁ A₀ w h h₁ h₀ hw0
  · exact start3_endpoint_of_A2_neg A₂ A₁ A₀ w (le_of_lt h) hw0 hw1 h₀ hsum

/-! ## The start-3 `v=w=1` quartic

Normalising `d₂ = 1` and substituting `g = d₃/(1−u)` factors `(1−u)⁴` out of the `v=w=1` value,
leaving the quartic `F = c₄g⁴ + c₃g³ + c₂g² + c₁g + c₀` in which `c₂` is the only negative
coefficient.  We record the coefficient facts that are provable; `F ≥ 0` itself is open. -/

/-- `c₃`'s inner factor is a sum of squares: `d₁² + 4d₁u − 2d₁ + 1 = (d₁−1)² + 4d₁u`. -/
theorem start3_c3_inner (d₁ u : ℝ) :
    d₁^2 + 4*d₁*u - 2*d₁ + 1 = (d₁ - 1)^2 + 4*d₁*u := by ring

/-- `c₃ = 4d₁(d₁+1)((d₁−1)² + 4d₁u) ≥ 0`. -/
theorem start3_c3_nonneg (d₁ u : ℝ) (hd₁ : 0 ≤ d₁) (hu : 0 ≤ u) :
    0 ≤ 4*d₁*(d₁ + 1)*((d₁ - 1)^2 + 4*d₁*u) := by positivity

/-- `c₀ = 2d₁⁴ ≥ 0` and `c₁ = 4d₁³(d₁+1) ≥ 0`. -/
theorem start3_c0_c1_nonneg (d₁ : ℝ) (hd₁ : 0 ≤ d₁) :
    0 ≤ 2*d₁^4 ∧ 0 ≤ 4*d₁^3*(d₁ + 1) := ⟨by positivity, by positivity⟩

/-- **`c₄ > 0`.**  The only negative contribution is `d₁²(14u − 5u² − 3)`, bounded below by
`−3d₁²` on `u ∈ [0,1]`, and absorbed by `d₁⁴ + 2d₁³ + 2d₁ + 1`. -/
theorem start3_c4_pos (d₁ u : ℝ) (hd₁ : 0 ≤ d₁) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 < 2*(d₁^4 + 2*d₁^3*u + 2*d₁^3 + d₁^2*(14*u - 5*u^2 - 3) + 2*d₁*u + 2*d₁ + 1) := by
  nlinarith [sq_nonneg (d₁^2 - 1), sq_nonneg (d₁ - 1), sq_nonneg d₁, mul_nonneg hd₁ hu0,
    mul_nonneg (mul_nonneg hd₁ hd₁) hu0, sq_nonneg (d₁^2 - d₁), mul_nonneg hu0 (sub_nonneg.mpr hu1),
    mul_nonneg (mul_nonneg hd₁ hd₁) (mul_nonneg hu0 (sub_nonneg.mpr hu1))]

/-- **`c₂ ≤ 0`** — the single negative coefficient of the quartic. -/
theorem start3_c2_nonpos (d₁ u : ℝ) (hd₁ : 0 ≤ d₁) (hu : 0 ≤ u) :
    -2*d₁^2*(3*d₁^2 + 4*d₁*u + 2*d₁ + 3) ≤ 0 := by
  have : 0 ≤ 2*d₁^2*(3*d₁^2 + 4*d₁*u + 2*d₁ + 3) := by positivity
  linarith

/-! ## The `u = 1` slice of the start-3 quartic

At `u = 1` the coefficients collapse: `c₃ = 4d₁(d₁+1)³` and `c₄ = 2(d₁+1)⁴`, because
`(d₁−1)² + 4d₁ = (d₁+1)²`.  Substituting `t = (d₁+1)g` then makes `F/2` a *homogeneous* binary
quartic in `(d₁,t)`,
`Q = d₁⁴ + 2d₁³t − 3d₁²t² + 2d₁t³ + t⁴`,
which is palindromic and admits an exact positive decomposition. -/

/-- At `u = 1` the inner factor of `c₃` is a perfect square: `(d₁−1)² + 4d₁ = (d₁+1)²`. -/
theorem start3_u1_c3_inner (d₁ : ℝ) : (d₁ - 1)^2 + 4*d₁ = (d₁ + 1)^2 := by ring

/-- **The palindromic certificate.**  The homogeneous quartic
`Q = d₁⁴ + 2d₁³t − 3d₁²t² + 2d₁t³ + t⁴` decomposes as
`Q = 3d₁²t² + (d₁−t)²(d₁² + 4d₁t + t²)`,
every summand nonnegative for `d₁, t ≥ 0`.  (It comes from `Q/(d₁t)² = (s+1)² − 6` with
`s = d₁/t + t/d₁ ≥ 2` by AM–GM, cleared of denominators.) -/
theorem start3_Q_certificate (d₁ t : ℝ) :
    d₁^4 + 2*d₁^3*t - 3*d₁^2*t^2 + 2*d₁*t^3 + t^4
      = 3*d₁^2*t^2 + (d₁ - t)^2 * (d₁^2 + 4*d₁*t + t^2) := by ring

/-- **`Q ≥ 0`**, hence `Q > 0` unless `d₁ = t = 0`. -/
theorem start3_Q_nonneg (d₁ t : ℝ) (hd₁ : 0 ≤ d₁) (ht : 0 ≤ t) :
    0 ≤ d₁^4 + 2*d₁^3*t - 3*d₁^2*t^2 + 2*d₁*t^3 + t^4 := by
  rw [start3_Q_certificate]
  have h1 : (0:ℝ) ≤ 3*d₁^2*t^2 := by positivity
  have h2 : (0:ℝ) ≤ (d₁ - t)^2 * (d₁^2 + 4*d₁*t + t^2) := by positivity
  linarith

/-- **The `u = 1` slice of the start-3 `v=w=1` quartic is nonnegative.**  With
`t = (d₁+1)g`, the quartic `F` at `u = 1` equals `2Q(d₁,t)`, so `start3_Q_nonneg` applies. -/
theorem start3_F_at_u1_nonneg (d₁ g : ℝ) (hd₁ : 0 ≤ d₁) (hg : 0 ≤ g) :
    0 ≤ 2*(d₁ + 1)^4 * g^4 + 4*d₁*(d₁ + 1)^3 * g^3 - 6*d₁^2*(d₁ + 1)^2 * g^2
        + 4*d₁^3*(d₁ + 1) * g + 2*d₁^4 := by
  have ht : 0 ≤ (d₁ + 1) * g := mul_nonneg (by linarith) hg
  have hQ := start3_Q_nonneg d₁ ((d₁ + 1) * g) hd₁ ht
  have hid : 2*(d₁ + 1)^4 * g^4 + 4*d₁*(d₁ + 1)^3 * g^3 - 6*d₁^2*(d₁ + 1)^2 * g^2
        + 4*d₁^3*(d₁ + 1) * g + 2*d₁^4
      = 2 * (d₁^4 + 2*d₁^3*((d₁ + 1)*g) - 3*d₁^2*((d₁ + 1)*g)^2
          + 2*d₁*((d₁ + 1)*g)^3 + ((d₁ + 1)*g)^4) := by ring
  rw [hid]; linarith

/-! ## The equality case of the quartic

At `d₁ = 1`, `u = 0` the quartic degenerates to `6g⁴ − 16g² + 8g + 2`, which factors as
`2(g−1)²(3g²+6g+1)` and so vanishes at `g = 1`.  Unwinding the substitutions, that point is
`p₁₂ = 0` with all three rates equal — the deterministic chain `3→2→1→exit`, i.e. `Erlang(3)`,
where `κ₃ = 5/6` is attained.  So the quartic is *tight*, and no strict/slack argument can prove
it; a certificate must vanish to second order there. -/

/-- **The equality-case factorisation.**  `6g⁴ − 16g² + 8g + 2 = 2(g−1)²(3g²+6g+1)`, exhibiting
the double root at `g = 1`. -/
theorem quartic_equality_factor (g : ℝ) :
    6*g^4 - 16*g^2 + 8*g + 2 = 2*(g - 1)^2 * (3*g^2 + 6*g + 1) := by ring

/-- The degenerate quartic is nonnegative for `g ≥ 0`, with equality exactly at `g = 1`. -/
theorem quartic_equality_nonneg (g : ℝ) (hg : 0 ≤ g) :
    0 ≤ 6*g^4 - 16*g^2 + 8*g + 2 := by
  rw [quartic_equality_factor]
  have h : (0:ℝ) ≤ 3*g^2 + 6*g + 1 := by positivity
  have h2 : (0:ℝ) ≤ (g - 1)^2 := sq_nonneg _
  nlinarith [mul_nonneg h2 h]

/-- Equality holds at `g = 1`: the quartic is exactly `0` there. -/
theorem quartic_equality_at_one : 6*(1:ℝ)^4 - 16*1^2 + 8*1 + 2 = 0 := by norm_num

/-- **`c₃` vanishes at the equality point.**  `c₃ = 4d₁(d₁+1)((d₁−1)² + 4d₁u)` is zero at
`d₁ = 1`, `u = 0` — which is why the `c₁g + c₃g³ ≥ 2√(c₁c₃)g²` pairing cannot work there. -/
theorem start3_c3_vanishes : 4*(1:ℝ)*(1 + 1)*(((1:ℝ) - 1)^2 + 4*1*0) = 0 := by norm_num

/-! ## The `u = 0` slice: an exact six-term certificate

At `u = 0` the quartic `F/2` has an exact decomposition into six manifestly nonnegative terms,
every one of which vanishes at the `Erlang(3)` point `d₁ = g = 1`.  This is the shape any proof of
the general case must take, since the inequality is tight there. -/

/-- **The `u = 0` certificate.**  An exact identity:
`F/2|_{u=0} = 2d₁g(d₁−g)² + 2d₁g⁴(d₁−1)² + 2d₁⁴g(g−1)² + d₁²g²(d₁g−1)² + g²(d₁²−g)² + d₁²(d₁−g²)²`.
All six summands vanish at `d₁ = g = 1`, matching the equality case. -/
theorem start3_u0_certificate (d₁ g : ℝ) :
    (2*(d₁^4 + 2*d₁^3 - 3*d₁^2 + 2*d₁ + 1)*g^4
        + 4*d₁*(d₁ + 1)*(d₁ - 1)^2*g^3
        - 2*d₁^2*(3*d₁^2 + 2*d₁ + 3)*g^2
        + 4*d₁^3*(d₁ + 1)*g + 2*d₁^4) / 2
      = 2*d₁*g*(d₁ - g)^2 + 2*d₁*g^4*(d₁ - 1)^2 + 2*d₁^4*g*(g - 1)^2
        + d₁^2*g^2*(d₁*g - 1)^2 + g^2*(d₁^2 - g)^2 + d₁^2*(d₁ - g^2)^2 := by
  ring

/-- **`F ≥ 0` at `u = 0`.**  Immediate from the certificate: every summand is nonnegative for
`d₁, g ≥ 0`. -/
theorem start3_F_at_u0_nonneg (d₁ g : ℝ) (hd₁ : 0 ≤ d₁) (hg : 0 ≤ g) :
    0 ≤ 2*(d₁^4 + 2*d₁^3 - 3*d₁^2 + 2*d₁ + 1)*g^4
        + 4*d₁*(d₁ + 1)*(d₁ - 1)^2*g^3
        - 2*d₁^2*(3*d₁^2 + 2*d₁ + 3)*g^2
        + 4*d₁^3*(d₁ + 1)*g + 2*d₁^4 := by
  have h := start3_u0_certificate d₁ g
  have hpos : 0 ≤ 2*d₁*g*(d₁ - g)^2 + 2*d₁*g^4*(d₁ - 1)^2 + 2*d₁^4*g*(g - 1)^2
      + d₁^2*g^2*(d₁*g - 1)^2 + g^2*(d₁^2 - g)^2 + d₁^2*(d₁ - g^2)^2 := by positivity
  linarith [h ▸ hpos]

/-- Each of the six terms vanishes at the `Erlang(3)` point `d₁ = g = 1`, so the certificate is
tight exactly where the conjecture predicts equality. -/
theorem start3_u0_certificate_tight :
    2*(1:ℝ)*1*(1 - 1)^2 + 2*1*1^4*(1 - 1)^2 + 2*1^4*1*(1 - 1)^2
      + 1^2*1^2*(1*1 - 1)^2 + 1^2*(1^2 - 1)^2 + 1^2*(1 - 1^2)^2 = 0 := by norm_num

/-! ## `F ≥ 0` for all `u ∈ [0,1]`: concavity in `u`

The quartic `F/2` is a *quadratic in `u`* with leading coefficient `−5d₁²g⁴ ≤ 0`.  So it is concave
in `u`, its minimum over `u ∈ [0,1]` is attained at an endpoint, and both endpoints are already
proved: `u = 0` by the six-term certificate `start3_F_at_u0_nonneg`, and `u = 1` by the palindromic
certificate `start3_F_at_u1_nonneg`.  This closes the last piece of the start-3 analysis. -/

/-- `F/2` as a quadratic in `u`: leading coefficient `−5d₁²g⁴`, and the `u = 0` and `u = 1` values
are exactly the two slices already certified. -/
theorem start3_F_quad_in_u (d₁ g u : ℝ) :
    (2*(d₁^4 + 2*d₁^3*u + 2*d₁^3 + d₁^2*(14*u - 5*u^2 - 3) + 2*d₁*u + 2*d₁ + 1)*g^4
        + 4*d₁*(d₁ + 1)*((d₁ - 1)^2 + 4*d₁*u)*g^3
        - 2*d₁^2*(3*d₁^2 + 4*d₁*u + 2*d₁ + 3)*g^2
        + 4*d₁^3*(d₁ + 1)*g + 2*d₁^4) / 2
      = (-(5*d₁^2*g^4)) * u^2
        + (2*d₁*g^2*(d₁^2*g^2 + 4*d₁^2*g - 2*d₁^2 + 7*d₁*g^2 + 4*d₁*g + g^2)) * u
        + (2*(d₁^4 + 2*d₁^3 - 3*d₁^2 + 2*d₁ + 1)*g^4
            + 4*d₁*(d₁ + 1)*(d₁ - 1)^2*g^3
            - 2*d₁^2*(3*d₁^2 + 2*d₁ + 3)*g^2
            + 4*d₁^3*(d₁ + 1)*g + 2*d₁^4) / 2 := by
  ring

/-- **The start-3 quartic is nonnegative for every `u ∈ [0,1]`.**  Concavity in `u` reduces to the
two endpoints, both certified. -/
theorem start3_F_nonneg (d₁ g u : ℝ) (hd₁ : 0 ≤ d₁) (hg : 0 ≤ g)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ (2*(d₁^4 + 2*d₁^3*u + 2*d₁^3 + d₁^2*(14*u - 5*u^2 - 3) + 2*d₁*u + 2*d₁ + 1)*g^4
        + 4*d₁*(d₁ + 1)*((d₁ - 1)^2 + 4*d₁*u)*g^3
        - 2*d₁^2*(3*d₁^2 + 4*d₁*u + 2*d₁ + 3)*g^2
        + 4*d₁^3*(d₁ + 1)*g + 2*d₁^4) / 2 := by
  set a : ℝ := -(5*d₁^2*g^4) with ha
  set b : ℝ := 2*d₁*g^2*(d₁^2*g^2 + 4*d₁^2*g - 2*d₁^2 + 7*d₁*g^2 + 4*d₁*g + g^2) with hb
  set c : ℝ := (2*(d₁^4 + 2*d₁^3 - 3*d₁^2 + 2*d₁ + 1)*g^4
      + 4*d₁*(d₁ + 1)*(d₁ - 1)^2*g^3 - 2*d₁^2*(3*d₁^2 + 2*d₁ + 3)*g^2
      + 4*d₁^3*(d₁ + 1)*g + 2*d₁^4) / 2 with hc
  rw [start3_F_quad_in_u]
  -- concave: leading coefficient ≤ 0
  have hane : a ≤ 0 := by rw [ha]; nlinarith [sq_nonneg (d₁*g^2), sq_nonneg d₁, sq_nonneg g]
  -- endpoint u = 0
  have h0 : 0 ≤ c := by
    rw [hc]
    have := start3_F_at_u0_nonneg d₁ g hd₁ hg
    linarith
  -- endpoint u = 1
  have h1 : 0 ≤ a + b + c := by
    have hF1 := start3_F_at_u1_nonneg d₁ g hd₁ hg
    have hid : a + b + c
        = (2*(d₁ + 1)^4 * g^4 + 4*d₁*(d₁ + 1)^3 * g^3 - 6*d₁^2*(d₁ + 1)^2 * g^2
            + 4*d₁^3*(d₁ + 1) * g + 2*d₁^4) / 2 := by
      rw [ha, hb, hc]; ring
    rw [hid]; linarith
  exact concave_quad_ge_endpoints a b c u hane hu0 hu1 h0 h1

/-! ## Start state 3: the `w`-reduction

The start-3 numerator is *quadratic in `w`* — degree `2`, against degree `4` in each of
`d₁,d₂,d₃,u,v`.  Writing it as `A w² + B w + C`:

* `C = 2d₁⁴d₂⁴(uv−1)⁴ ≥ 0` (at `w = 0` state `3` exits at once, so the law is `Exp(d₃)` and the
  ratio is `1 > 5/6`);
* `B = −4d₁d₂d₃(uv−1)·Φ` with `Φ ≥ 0` observed, and `−(uv−1) > 0` on the admissible set;
* `A` is sign-indefinite.

So the same dichotomy applies as before: where `A ≥ 0` the numerator is nonnegative termwise, and
where `A < 0` it is concave in `w`, hence bounded below by its values at `w = 0` and `w = 1`.  This
bypasses the quartic-in-`v` obstruction entirely. -/

/-- `C = 2d₁⁴d₂⁴(uv−1)⁴ ≥ 0`: the `w = 0` value, where state `3` exits immediately. -/
theorem start3_w0_nonneg (d₁ d₂ u v : ℝ) : 0 ≤ 2*d₁^4*d₂^4*(u*v - 1)^4 := by positivity

/-- The prefactor of `Φ` in `B` is nonnegative on the admissible set `uv < 1`. -/
theorem start3_B_prefactor_nonneg (d₁ d₂ d₃ u v : ℝ) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (hd₃ : 0 ≤ d₃) (huv : u*v ≤ 1) : 0 ≤ -4*d₁*d₂*d₃*(u*v - 1) := by
  have h : 0 ≤ 1 - u*v := by linarith
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hd₁ hd₂) hd₃) h]

/-- **The `w`-reduction for start state 3.**  Given `C ≥ 0`, `B ≥ 0` and the value at `w = 1`
nonnegative, the numerator is nonnegative for all `w ∈ [0,1]` — both branches of the dichotomy on
the sign of `A`. -/
theorem start3_w_reduction (A B C w : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hone : 0 ≤ A + B + C) :
    0 ≤ A * w^2 + B * w + C := by
  rcases le_or_gt 0 A with h | h
  · exact quad_nonneg_of_coeffs A B C w h hB hC hw0
  · exact concave_quad_ge_endpoints A B C w (le_of_lt h) hw0 hw1 hC hone

/-- **The `v = 0` slice of the `w = 1` endpoint** reuses the palindromic certificate: its bracket
is `Q(d₂,d₃) = d₂⁴ + 2d₂³d₃ − 3d₂²d₃² + 2d₂d₃³ + d₃⁴`, so `start3_Q_nonneg` applies with
`(d₁,t) ↦ (d₂,d₃)`. -/
theorem start3_w1_v0_nonneg (d₁ d₂ d₃ : ℝ) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃) :
    0 ≤ 2*d₁^4*(d₂^4 + 2*d₂^3*d₃ - 3*d₂^2*d₃^2 + 2*d₂*d₃^3 + d₃^4) := by
  have hQ := start3_Q_nonneg d₂ d₃ hd₂ hd₃
  have h4 : (0:ℝ) ≤ 2*d₁^4 := by positivity
  exact mul_nonneg h4 hQ

/-! ## `Φ ≥ 0`: the `B`-bracket of the start-3 `w`-reduction

`Φ` is *quadratic in `u`* with leading coefficient `d₁²d₂²v²(d₁ + d₂v + 2d₃) ≥ 0`, so it is convex
in `u` and its minimum over `[0,1]` is at an endpoint or the interior vertex.  Both endpoints have
clean certificates, recorded here. -/

/-- `Φ`'s leading coefficient in `u` is nonnegative, so `Φ` is convex in `u`. -/
theorem Phi_lead_u_nonneg (d₁ d₂ d₃ v : ℝ) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (hv : 0 ≤ v) : 0 ≤ d₁^2*d₂^2*v^2*(d₁ + d₂*v + 2*d₃) := by
  have : 0 ≤ d₁ + d₂*v + 2*d₃ := by
    have := mul_nonneg hd₂ hv
    linarith
  positivity

/-- **A positive-definite quadratic used twice below**: `8d₂² − 12d₂d₃ + 27d₃²` has discriminant
`144 − 864 < 0`, and explicitly `= 8(d₂ − 3d₃/4)² + (45/2)d₃²`. -/
theorem pd_8_12_27 (d₂ d₃ : ℝ) :
    8*d₂^2 - 12*d₂*d₃ + 27*d₃^2 = 8*(d₂ - 3*d₃/4)^2 + (45/2)*d₃^2 := by ring

/-- **`Φ` at `u = 0`.**  After factoring, the inner form is
`d₁²((d₂−d₃)² + 2d₃²) + d₁d₂d₃(3d₃ − 2d₂) + 3d₂²d₃²`, a quadratic in `d₁` whose discriminant is
`−d₂²d₃²(8d₂² − 12d₂d₃ + 27d₃²) < 0` by `pd_8_12_27`; hence it is positive definite.
Formalization shows no sign conditions on `d₁,d₂,d₃` are needed — it holds for all reals. -/
theorem Phi_at_u0_inner_nonneg (d₁ d₂ d₃ : ℝ) :
    0 ≤ d₁^2*((d₂ - d₃)^2 + 2*d₃^2) + d₁*d₂*d₃*(3*d₃ - 2*d₂) + 3*d₂^2*d₃^2 := by
  nlinarith [sq_nonneg (d₁*(d₂ - d₃)), sq_nonneg (d₁*d₃), sq_nonneg (d₂*d₃),
    sq_nonneg (2*d₁*d₃ - d₂*d₃), sq_nonneg (d₁*d₂ - d₂*d₃),
    sq_nonneg (2*d₁*d₃ - 3*d₂*d₃/2), sq_nonneg (d₁*d₂ - 2*d₂*d₃)]

/-- **`Φ` at `u = 1`: the `d₁³` part.**  `d₂²(v−1)² + 2d₂d₃(v−1) + 3d₃² = (d₂(v−1)+d₃)² + 2d₃²`,
manifestly nonnegative — the `(v−1)` sign does no harm because it is completed into a square. -/
theorem Phi_at_u1_lead (d₂ d₃ v : ℝ) :
    d₂^2*(v - 1)^2 + 2*d₂*d₃*(v - 1) + 3*d₃^2 = (d₂*(v - 1) + d₃)^2 + 2*d₃^2 := by ring

/-- Consequently that part is nonnegative. -/
theorem Phi_at_u1_lead_nonneg (d₂ d₃ v : ℝ) :
    0 ≤ d₂^2*(v - 1)^2 + 2*d₂*d₃*(v - 1) + 3*d₃^2 := by
  rw [Phi_at_u1_lead]; positivity

/-! ## The `v = w = 1` endpoint is the already-proved quartic

Substituting `u = s/v` makes the `w = 1` expression a polynomial of degree `2` in `v`.  Its `v = 1`
value, after the substitution `h = d₃/(1−s)` that strips the `(s−1)` powers, turns out to be
`d₂⁸·F(d₁/d₂, h/d₂, s)` — the *same* quartic already settled by `start3_F_nonneg`.  So this endpoint
needs no new work. -/

/-- **The `v = w = 1` endpoint equals `d₂⁸·F`.**  An exact identity: the quartic in `h` arising at
`v = w = 1` is `F`'s quartic under `(d₁, g, u) ↦ (d₁/d₂, h/d₂, s)`, scaled by `d₂⁸`.  Stated here in
cleared form, so no division appears. -/
theorem start3_v1w1_eq_F (d₁ d₂ h s : ℝ) :
    (-2*(-d₁^4 - 2*d₁^3*d₂*s - 2*d₁^3*d₂ + 5*d₁^2*d₂^2*s^2 - 14*d₁^2*d₂^2*s
        + 3*d₁^2*d₂^2 - 2*d₁*d₂^3*s - 2*d₁*d₂^3 - d₂^4)) * h^4
      + (4*d₁*d₂*(d₁ + d₂)*(d₁^2 + 4*d₁*d₂*s - 2*d₁*d₂ + d₂^2)) * h^3
      + (-2*d₁^2*d₂^2*(3*d₁^2 + 4*d₁*d₂*s + 2*d₁*d₂ + 3*d₂^2)) * h^2
      + (4*d₁^3*d₂^3*(d₁ + d₂)) * h
      + 2*d₁^4*d₂^4
      = 2*(d₁^4 + 2*d₁^3*d₂*s + 2*d₁^3*d₂ + d₁^2*d₂^2*(14*s - 5*s^2 - 3)
            + 2*d₁*d₂^3*s + 2*d₁*d₂^3 + d₂^4) * h^4
        + 4*d₁*d₂*(d₁ + d₂)*((d₁ - d₂)^2 + 4*d₁*d₂*s) * h^3
        - 2*d₁^2*d₂^2*(3*d₁^2 + 4*d₁*d₂*s + 2*d₁*d₂ + 3*d₂^2) * h^2
        + 4*d₁^3*d₂^3*(d₁ + d₂) * h + 2*d₁^4*d₂^4 := by
  ring

/-- **The `v = w = 1` endpoint is nonnegative.**  It is the homogenised form of the quartic
`start3_F_nonneg`, obtained by clearing `d₂` from `F(d₁/d₂, h/d₂, s)`; every coefficient matches
after the scaling, so nonnegativity transfers. -/
theorem start3_v1w1_nonneg (d₁ d₂ h s : ℝ) (hd₁ : 0 ≤ d₁) (hd₂ : 0 < d₂) (hh : 0 ≤ h)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ 2*(d₁^4 + 2*d₁^3*d₂*s + 2*d₁^3*d₂ + d₁^2*d₂^2*(14*s - 5*s^2 - 3)
            + 2*d₁*d₂^3*s + 2*d₁*d₂^3 + d₂^4) * h^4
        + 4*d₁*d₂*(d₁ + d₂)*((d₁ - d₂)^2 + 4*d₁*d₂*s) * h^3
        - 2*d₁^2*d₂^2*(3*d₁^2 + 4*d₁*d₂*s + 2*d₁*d₂ + 3*d₂^2) * h^2
        + 4*d₁^3*d₂^3*(d₁ + d₂) * h + 2*d₁^4*d₂^4 := by
  have hD : 0 ≤ d₁ / d₂ := div_nonneg hd₁ (le_of_lt hd₂)
  have hg : 0 ≤ h / d₂ := div_nonneg hh (le_of_lt hd₂)
  have hF := start3_F_nonneg (d₁ / d₂) (h / d₂) s hD hg hs0 hs1
  have hd₂ne : d₂ ≠ 0 := ne_of_gt hd₂
  have hpow : (0:ℝ) < d₂^8 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hF (le_of_lt hpow)
  -- clear the denominators: d₂⁸ · F(d₁/d₂, h/d₂, s) is the displayed expression
  have hid : d₂^8 * ((2*((d₁/d₂)^4 + 2*(d₁/d₂)^3*s + 2*(d₁/d₂)^3
        + (d₁/d₂)^2*(14*s - 5*s^2 - 3) + 2*(d₁/d₂)*s + 2*(d₁/d₂) + 1)*(h/d₂)^4
      + 4*(d₁/d₂)*((d₁/d₂) + 1)*(((d₁/d₂) - 1)^2 + 4*(d₁/d₂)*s)*(h/d₂)^3
      - 2*(d₁/d₂)^2*(3*(d₁/d₂)^2 + 4*(d₁/d₂)*s + 2*(d₁/d₂) + 3)*(h/d₂)^2
      + 4*(d₁/d₂)^3*((d₁/d₂) + 1)*(h/d₂) + 2*(d₁/d₂)^4) / 2)
      = (2*(d₁^4 + 2*d₁^3*d₂*s + 2*d₁^3*d₂ + d₁^2*d₂^2*(14*s - 5*s^2 - 3)
            + 2*d₁*d₂^3*s + 2*d₁*d₂^3 + d₂^4) * h^4
        + 4*d₁*d₂*(d₁ + d₂)*((d₁ - d₂)^2 + 4*d₁*d₂*s) * h^3
        - 2*d₁^2*d₂^2*(3*d₁^2 + 4*d₁*d₂*s + 2*d₁*d₂ + 3*d₂^2) * h^2
        + 4*d₁^3*d₂^3*(d₁ + d₂) * h + 2*d₁^4*d₂^4) / 2 := by
    field_simp
  nlinarith [hscaled, hid]

/-! ## The `Φ` vertex estimate: the factored form

Writing `A = d₁²d₂²v²·a` and `B = −d₁d₂v·b` with

  `a = d₁ + d₂v + 2d₃`,  `b = R − Q·d₃ − P·d₃²`,
  `P = 3(2d₁ + d₂(1+v))`,  `Q = 2(d₁² − d₁d₂(1−v) + d₂²v)`,  `R = 2d₁d₂(d₁ + d₂v)`,

the estimate `4AC − B² ≥ 0` becomes `4aC − b² ≥ 0`, needed when `b ≥ 0`.  The facts below are the
provable parts; the implication `b ≥ 0 → 4aC − b² ≥ 0` is the one piece still open. -/

/-- `a = d₁ + d₂v + 2d₃ > 0`. -/
theorem Phi_a_pos (d₁ d₂ d₃ v : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃) (hv : 0 ≤ v) :
    0 < d₁ + d₂*v + 2*d₃ := by
  have := mul_nonneg hd₂ hv
  linarith

/-- **The `b`-factorisation.**  `b = R − Q·d₃ − P·d₃²` with the stated `P, Q, R`. -/
theorem Phi_b_factored (d₁ d₂ d₃ v : ℝ) :
    2*d₁^2*d₂ - 2*d₁^2*d₃ + 2*d₁*d₂^2*v - 2*d₁*d₂*d₃*v + 2*d₁*d₂*d₃ - 6*d₁*d₃^2
      - 2*d₂^2*d₃*v - 3*d₂*d₃^2*v - 3*d₂*d₃^2
      = 2*d₁*d₂*(d₁ + d₂*v)
        - 2*(d₁^2 - d₁*d₂*(1 - v) + d₂^2*v)*d₃
        - 3*(2*d₁ + d₂*(1 + v))*d₃^2 := by
  ring

/-- `P = 3(2d₁ + d₂(1+v)) > 0`, so `b` is a downward parabola in `d₃`: `b ≥ 0` bounds `d₃`. -/
theorem Phi_P_pos (d₁ d₂ v : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 ≤ d₂) (hv : 0 ≤ v) :
    0 < 3*(2*d₁ + d₂*(1 + v)) := by
  have := mul_nonneg hd₂ hv
  linarith

/-- **`Q`'s discriminant.**  As a quadratic in `d₁`, `Q/2 = d₁² − d₁d₂(1−v) + d₂²v` has
discriminant `d₂²((1−v)² − 4v) = d₂²(v² − 6v + 1)`, which is negative for
`v > 3 − 2√2 ≈ 0.1716`.  So `Q` is *not* always nonnegative — the reason the cruder bound
`P d₃² ≤ R` cannot replace `b ≥ 0`. -/
theorem Phi_Q_disc (d₂ v : ℝ) :
    (d₂*(1 - v))^2 - 4*(d₂^2*v) = d₂^2*(v^2 - 6*v + 1) := by ring

/-- **The vertex reduction.**  With `A = d₁²d₂²v²a` and `B = −d₁d₂vb`,
`4AC − B² = d₁²d₂²v²(4aC − b²)`, so the estimate reduces to the bracket. -/
theorem Phi_vertex_reduction (d₁ d₂ v a b C : ℝ) :
    4*(d₁^2*d₂^2*v^2*a)*C - (-(d₁*d₂*v*b))^2
      = d₁^2*d₂^2*v^2*(4*a*C - b^2) := by
  ring

/-! ### The vertex estimate: `b ≥ 0 ⟹ 4aC − b² ≥ 0`

This is the last step of the start-state-3 argument.  The whole content is a linear
certificate.  Writing

* `P = 3(2d₁ + d₂(1+v))`,
* `S = (d₁+d₂)(d₁+d₂v)`,
* `G = 8S² + 12d₂S(1−v)d₃ − P²d₃²`,

the bracket factors as `4aC − b² = d₃²·G` (`Phi_bracket_factor`), and `G` is a
*linear* combination of the hypothesis and manifestly positive pieces:

  `G = P·b + K + 6M·d₃`,  `K = 2(d₁+d₂v)(4d₁³+4d₁²d₂v+2d₁²d₂+5d₁d₂²v+d₁d₂²+4d₂³v)`,
  `M = 2d₁³ + d₁²d₂(1+v) + d₁d₂²(1+2v) + 3d₂³v − v²d₂²(d₁+d₂)`.

`K > 0` by inspection; `M > 0` because `M − (2d₁³+d₁²d₂(1+v)+d₁d₂²(1+v)+2d₂³v)
= v(1−v)d₂²(d₁+d₂) ≥ 0` on `0 ≤ v ≤ 1`.  Note this needs `v ≤ 1`: `M` genuinely goes
negative for large `v`, and unrestricted `4aC − b²` reaches `≈ −3.7·10²⁶`. -/

/-- Abbreviation for the quadratic `C` appearing in `Φ`. -/
noncomputable def PhiC (d₁ d₂ d₃ v : ℝ) : ℝ :=
  d₁^3*d₂^2 - 2*d₁^3*d₂*d₃ + 3*d₁^3*d₃^2 + d₁^2*d₂^3*v - 2*d₁^2*d₂^2*d₃*v
    + 3*d₁^2*d₂*d₃^2*v - 2*d₁*d₂^3*d₃*v + 3*d₁*d₂^2*d₃^2*v + 3*d₂^3*d₃^2*v

/-- `a = d₁ + d₂v + 2d₃`. -/
noncomputable def Phia (d₁ d₂ d₃ v : ℝ) : ℝ := d₁ + d₂*v + 2*d₃

/-- `b = R − Q d₃ − P d₃²`. -/
noncomputable def Phib (d₁ d₂ d₃ v : ℝ) : ℝ :=
  2*d₁*d₂*(d₁ + d₂*v) - 2*(d₁^2 - d₁*d₂*(1 - v) + d₂^2*v)*d₃
    - 3*(2*d₁ + d₂*(1 + v))*d₃^2

/-- `G`, the bracket with the forced factor `d₃²` removed. -/
noncomputable def PhiG (d₁ d₂ d₃ v : ℝ) : ℝ :=
  8*((d₁+d₂)*(d₁+d₂*v))^2 + 12*d₂*((d₁+d₂)*(d₁+d₂*v))*(1-v)*d₃
    - (3*(2*d₁ + d₂*(1 + v)))^2*d₃^2

/-- The positive constant term of the certificate. -/
noncomputable def PhiK (d₁ d₂ v : ℝ) : ℝ :=
  2*(d₁+d₂*v)*(4*d₁^3 + 4*d₁^2*d₂*v + 2*d₁^2*d₂ + 5*d₁*d₂^2*v + d₁*d₂^2 + 4*d₂^3*v)

/-- The coefficient of `d₃` in the certificate (positive for `0 ≤ v ≤ 1`). -/
noncomputable def PhiM (d₁ d₂ v : ℝ) : ℝ :=
  2*d₁^3 + d₁^2*d₂*(1+v) + d₁*d₂^2*(1+2*v) + 3*d₂^3*v - v^2*d₂^2*(d₁+d₂)

/-- **The forced factor.**  `4aC − b² = d₃²·G`: every monomial of the bracket carries `d₃²`. -/
theorem Phi_bracket_factor (d₁ d₂ d₃ v : ℝ) :
    4 * Phia d₁ d₂ d₃ v * PhiC d₁ d₂ d₃ v - (Phib d₁ d₂ d₃ v)^2
      = d₃^2 * PhiG d₁ d₂ d₃ v := by
  unfold Phia PhiC Phib PhiG; ring

/-- **The linear certificate.**  `G = P·b + K + 6M·d₃`.  Both `b`-quadratics have leading
coefficient a negative multiple of `P`, so `P²b − P·G` is linear in `d₃`; dividing by `P`
gives this identity, in which `b` enters *linearly*. -/
theorem PhiG_certificate (d₁ d₂ d₃ v : ℝ) :
    PhiG d₁ d₂ d₃ v
      = 3*(2*d₁ + d₂*(1 + v)) * Phib d₁ d₂ d₃ v + PhiK d₁ d₂ v + 6 * PhiM d₁ d₂ v * d₃ := by
  unfold PhiG Phib PhiK PhiM; ring

/-- `K > 0`: a product of two sums of positive monomials. -/
theorem PhiK_pos (d₁ d₂ v : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 ≤ d₂) (hv : 0 ≤ v) :
    0 < PhiK d₁ d₂ v := by
  unfold PhiK
  have h1 : 0 < d₁ + d₂*v := by nlinarith [mul_nonneg hd₂ hv]
  have h2 : 0 < 4*d₁^3 + 4*d₁^2*d₂*v + 2*d₁^2*d₂ + 5*d₁*d₂^2*v + d₁*d₂^2 + 4*d₂^3*v := by
    nlinarith [mul_nonneg (mul_nonneg hd₂ hd₂) hv, mul_nonneg hd₂ hv,
      mul_nonneg (mul_nonneg hd₂ hd₂) hd₂, sq_nonneg d₁, mul_pos hd₁ hd₁,
      mul_nonneg (mul_nonneg (le_of_lt hd₁) hd₂) hv,
      mul_nonneg (mul_nonneg (le_of_lt hd₁) hd₂) hd₂]
  positivity

/-- **The lower bound for `M`.**  `M − (2d₁³+d₁²d₂(1+v)+d₁d₂²(1+v)+2d₂³v) = v(1−v)d₂²(d₁+d₂)`. -/
theorem PhiM_lower_identity (d₁ d₂ v : ℝ) :
    PhiM d₁ d₂ v - (2*d₁^3 + d₁^2*d₂*(1+v) + d₁*d₂^2*(1+v) + 2*d₂^3*v)
      = v*(1-v)*d₂^2*(d₁+d₂) := by
  unfold PhiM; ring

/-- `M > 0` for `0 ≤ v ≤ 1`.  The restriction `v ≤ 1` is essential. -/
theorem PhiM_pos (d₁ d₂ v : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 ≤ d₂)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : 0 < PhiM d₁ d₂ v := by
  have hid := PhiM_lower_identity d₁ d₂ v
  have hslack : 0 ≤ v*(1-v)*d₂^2*(d₁+d₂) := by
    have h1 : 0 ≤ 1 - v := by linarith
    have h2 : 0 ≤ d₁ + d₂ := by linarith
    positivity
  have hlow : 0 < 2*d₁^3 + d₁^2*d₂*(1+v) + d₁*d₂^2*(1+v) + 2*d₂^3*v := by
    have e1 : 0 ≤ d₁^2*d₂*(1+v) := by positivity
    have e2 : 0 ≤ d₁*d₂^2*(1+v) := by positivity
    have e3 : 0 ≤ 2*d₂^3*v := by positivity
    have e4 : 0 < 2*d₁^3 := by positivity
    linarith
  linarith

/-- **`G > 0` under the hypothesis `b ≥ 0`.** -/
theorem PhiG_pos_of_b_nonneg (d₁ d₂ d₃ v : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 ≤ d₂)
    (hd₃ : 0 ≤ d₃) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hb : 0 ≤ Phib d₁ d₂ d₃ v) :
    0 < PhiG d₁ d₂ d₃ v := by
  have hP : (0:ℝ) < 3*(2*d₁ + d₂*(1 + v)) := Phi_P_pos d₁ d₂ v hd₁ hd₂ hv0
  have hPb : 0 ≤ 3*(2*d₁ + d₂*(1 + v)) * Phib d₁ d₂ d₃ v :=
    mul_nonneg (le_of_lt hP) hb
  have hK : 0 < PhiK d₁ d₂ v := PhiK_pos d₁ d₂ v hd₁ hd₂ hv0
  have hM : 0 < PhiM d₁ d₂ v := PhiM_pos d₁ d₂ v hd₁ hd₂ hv0 hv1
  have hMd : 0 ≤ 6 * PhiM d₁ d₂ v * d₃ := by
    have := mul_nonneg (le_of_lt hM) hd₃; linarith
  rw [PhiG_certificate]; linarith

/-- **The vertex estimate.**  `b ≥ 0 ⟹ 4aC − b² ≥ 0`, for `d₁ > 0`, `d₂, d₃ ≥ 0`,
`0 ≤ v ≤ 1`.  This is the final open item in the start-state-3 case at `s = 3`, hence
the last step of Conjecture 1 for `k = 2`, `s = 3`. -/
theorem Phi_vertex_estimate (d₁ d₂ d₃ v : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 ≤ d₂)
    (hd₃ : 0 ≤ d₃) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hb : 0 ≤ Phib d₁ d₂ d₃ v) :
    0 ≤ 4 * Phia d₁ d₂ d₃ v * PhiC d₁ d₂ d₃ v - (Phib d₁ d₂ d₃ v)^2 := by
  rw [Phi_bracket_factor]
  have hG := PhiG_pos_of_b_nonneg d₁ d₂ d₃ v hd₁ hd₂ hd₃ hv0 hv1 hb
  have : (0:ℝ) ≤ d₃^2 := sq_nonneg d₃
  exact mul_nonneg this (le_of_lt hG)

/-- **Consequence: the discriminant of `Φ` is nonpositive at an admissible vertex.**
With `A = d₁²d₂²v²a`, `B = −d₁d₂vb`, `4AC − B² = d₁²d₂²v²(4aC − b²) ≥ 0`. -/
theorem Phi_discriminant_nonneg (d₁ d₂ d₃ v : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 ≤ d₂)
    (hd₃ : 0 ≤ d₃) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hb : 0 ≤ Phib d₁ d₂ d₃ v) :
    0 ≤ 4*(d₁^2*d₂^2*v^2 * Phia d₁ d₂ d₃ v) * PhiC d₁ d₂ d₃ v
          - (-(d₁*d₂*v * Phib d₁ d₂ d₃ v))^2 := by
  rw [Phi_vertex_reduction]
  have h := Phi_vertex_estimate d₁ d₂ d₃ v hd₁ hd₂ hd₃ hv0 hv1 hb
  have : (0:ℝ) ≤ d₁^2*d₂^2*v^2 := by positivity
  exact mul_nonneg this h

end SSP.Chain
