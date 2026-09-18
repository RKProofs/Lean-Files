import Mathlib

/-!
# Toward the phase-type moment dictionary: the matrix semigroup

Groundwork for proving, rather than assuming, the moment identities used by
`SSPLean.AldousShepp`:

```
  ∫₀^∞ (exp(t(Q−I)) 𝟙)ᵢ dt = (N𝟙)ᵢ ,        ∫₀^∞ t·(exp(t(Q−I)) 𝟙)ᵢ dt = (N²𝟙)ᵢ ,
```

where `N = (I−Q)⁻¹`.  Together with the tail formula `E[Xᵏ] = k∫tᵏ⁻¹P(X>t)dt` these are the
dictionary `E_i[X] = (N𝟙)ᵢ`, `E_i[X²] = 2(N²𝟙)ᵢ` that `AbsorptionMoments` currently assumes.

## The mechanism

The proof needs no Neumann series.  Since `G := Q − I` satisfies

```
  G·N = (Q − I)(I − Q)⁻¹ = −I                       (`mul_inv_eq_neg_one`)
```

the function `F(t) := (exp(tG)·N𝟙)ᵢ` has derivative `(exp(tG)·G·N𝟙)ᵢ = −(exp(tG)𝟙)ᵢ`, i.e. `F`
is an antiderivative of the negated integrand.  So FTC-2 on `(0,∞)` gives
`∫₀^∞ (exp(tG)𝟙)ᵢ = F(0) − F(∞) = (N𝟙)ᵢ`, provided `F(∞) = 0`.  One differentiation, one limit.

## Status

**Both moment identities are proved.**  For `‖Q‖ ≤ θ < 1` in the `L∞` operator norm and `I − Q`
invertible, with `N = (I−Q)⁻¹`:

```
  ∫₀^∞ (exp(t(Q−I))·𝟙)ᵢ dt  = (N𝟙)ᵢ          (`integral_survival`)
  ∫₀^∞ (exp(t(Q−I))·N𝟙)ᵢ dt = (N²𝟙)ᵢ         (`integral_resolvent_sq`)
```

both instances of the general `integral_resolvent`.  So, given that the survival function of the
absorption time is `t ↦ (exp(t(Q−I))𝟙)ᵢ` — which is what *defines* a phase-type law rather than
a theorem about one — the moment dictionary

```
  E_i[X] = (N𝟙)ᵢ ,        E_i[X²] = 2(N²𝟙)ᵢ
```

follows from the tail formulas `E[X] = ∫P(X>t)dt` and `E[X²] = 2∫t·P(X>t)dt`.

The second moment costs nothing extra: generalising the antiderivative to an arbitrary vector
`y` gives `∫(exp(tG)y)ᵢ = (Ny)ᵢ`, and `y := N𝟙` is the `(N²𝟙)ᵢ` case.  No integration by parts.

Supporting results, several absent from Mathlib: `norm_exp_le` (`‖exp x‖ ≤ exp ‖x‖` for a general
normed algebra), `exp_smul_one` (`exp(c•1) = (exp c)•1`), `exp_smul_sub_one` (the scalar-shift
factorisation), `norm_exp_smul_sub_one_le`, and the FTC-2 inputs `tendsto_survival_zero`,
`integrableOn_survival`.

`norm_exp_le` alone does *not* give decay — it yields `‖exp(tG)‖ ≤ exp(t‖G‖)`, which grows.  The
factorisation is what turns it into `exp(−t(1−θ))`.

**Connection to the `rowSum` interface.**  `SSPLean.MomentBridge` restates both identities in
the discrete `Nmat`/`rowSum` form used by `SSPLean.QSequencePaths` and `SSPLean.AldousShepp`:
`integral_eq_rowSum` and `integral_eq_rowSum2`.

**What is still assumed.**  `SSPLean.AldousShepp` continues to bundle the dictionary into
`AbsorptionMoments`, because the remaining link is measure-theoretic rather than algebraic: the
tail formulas `E[X] = ∫₀^∞P(X>t)dt` and `E[X²] = 2∫₀^∞t·P(X>t)dt`, which need Mathlib's
layer-cake theorem (`lintegral_eq_lintegral_meas_lt`) and a weighted version of it, plus a
probability space carrying `X`.  Everything on the matrix side is now proved.
-/

open scoped Matrix.Norms.Operator
open NormedSpace Matrix MeasureTheory

set_option autoImplicit false

namespace SSP.Semigroup

/-- **Entry extraction as a continuous linear functional.**  `A ↦ (A·y)ᵢ` is linear in `A` and
bounded by `‖y‖·‖A‖`, since `‖A·y‖ ≤ ‖A‖‖y‖` for the `L∞` operator norm and the `i`-th
coordinate is dominated by the sup norm.

This is what lets a derivative computed in the matrix Banach algebra be pushed down to a
scalar-valued derivative. -/
noncomputable def rowFun {s : ℕ} (y : Fin s → ℝ) (i : Fin s) :
    Matrix (Fin s) (Fin s) ℝ →L[ℝ] ℝ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun A => (A.mulVec y) i
      map_add' := fun A B => by simp [Matrix.add_mulVec]
      map_smul' := fun c A => by simp [Matrix.smul_mulVec] }
    ⟨‖y‖, fun A => by
      calc ‖(A.mulVec y) i‖ ≤ ‖A.mulVec y‖ := norm_le_pi_norm _ i
        _ ≤ ‖A‖ * ‖y‖ := Matrix.linfty_opNorm_mulVec A y
        _ = ‖y‖ * ‖A‖ := mul_comm _ _⟩

@[simp] lemma rowFun_apply {s : ℕ} (y : Fin s → ℝ) (i : Fin s)
    (A : Matrix (Fin s) (Fin s) ℝ) : rowFun y i A = (A.mulVec y) i := rfl

/-- **The semigroup derivative, in scalar form.**

`d/dt (exp(tG)·y)ᵢ = (exp(tG)·G·y)ᵢ`.  Obtained by composing `hasDerivAt_exp_smul_const` — the
derivative of `t ↦ exp(t•G)` in the matrix algebra — with the functional `rowFun`. -/
theorem hasDerivAt_mulVec_exp {s : ℕ} (G : Matrix (Fin s) (Fin s) ℝ) (y : Fin s → ℝ)
    (i : Fin s) (t : ℝ) :
    HasDerivAt (fun u => ((NormedSpace.exp (u • G)).mulVec y) i)
      (((NormedSpace.exp (t • G) * G).mulVec y) i) t :=
  (rowFun y i).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const (𝕂 := ℝ) G t)

/-- **`G·N = −I`.**  With `G = Q − I` and `N = (I−Q)⁻¹`, the generator and the fundamental
matrix compose to `−I`.  This is what makes the antiderivative in the file header work: it turns
`exp(tG)·G·N𝟙` into `−exp(tG)𝟙`. -/
theorem mul_inv_eq_neg_one {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (hu : IsUnit (1 - Q)) :
    (Q - 1) * (1 - Q)⁻¹ = -1 := by
  have h : (Q - 1 : Matrix (Fin s) (Fin s) ℝ) = -(1 - Q) := by abel
  rw [h, neg_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]

/-- **The antiderivative property.**  `F(t) := (exp(tG)·N𝟙)ᵢ` has derivative
`−(exp(tG)·𝟙)ᵢ`, so `F` is an antiderivative of the negated survival function.

Combining `hasDerivAt_mulVec_exp` with `mul_inv_eq_neg_one`.  Given
`Tendsto F atTop (𝓝 0)` and integrability, `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`
would now yield `∫₀^∞ (exp(tG)𝟙)ᵢ = (N𝟙)ᵢ` — see the file header for why the decay is not yet
available. -/
theorem hasDerivAt_survival_antiderivative {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hu : IsUnit (1 - Q)) (i : Fin s) (t : ℝ) :
    HasDerivAt (fun u => ((NormedSpace.exp (u • (Q - 1))).mulVec
        ((1 - Q)⁻¹.mulVec (fun _ => 1))) i)
      (-(((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => 1)) i)) t := by
  have h := hasDerivAt_mulVec_exp (Q - 1) ((1 - Q)⁻¹.mulVec (fun _ => 1)) i t
  convert h using 1
  -- `(Q−1) *ᵥ (N 𝟙) = ((Q−1) * N) *ᵥ 𝟙 = (−1) *ᵥ 𝟙 = −𝟙`
  -- collapse `G *ᵥ (N *ᵥ 𝟙)` to `(G * N) *ᵥ 𝟙 = (−1) *ᵥ 𝟙 = −𝟙`
  rw [Matrix.mulVec_mulVec, mul_assoc, mul_inv_eq_neg_one Q hu, mul_neg, mul_one]
  simp [Matrix.neg_mulVec]

/-! ## Norm bounds on the matrix exponential

Mathlib has no `‖exp x‖ ≤ exp ‖x‖` for a general normed algebra — only summability of the
exponential series.  It is proved here from `NormedSpace.exp_eq_tsum`, and is the first of the
two analytic inputs the decay argument needs. -/

/-- `‖1‖ ≤ 1` for the `L∞` operator norm.  Needed because `Matrix (Fin s) (Fin s) ℝ` with this
norm is **not** a `NormOneClass` instance, so `norm_pow_le` is unavailable at `n = 0`.  (In fact
`‖1‖ = 1` for `s ≥ 1` and `‖1‖ = 0` for `s = 0`; only `≤ 1` is needed.) -/
lemma norm_one_le (s : ℕ) : ‖(1 : Matrix (Fin s) (Fin s) ℝ)‖ ≤ 1 := by
  rw [show (1 : Matrix (Fin s) (Fin s) ℝ) = Matrix.diagonal (fun _ => (1:ℝ)) by
        ext i j; simp [Matrix.one_apply, Matrix.diagonal]]
  rw [Matrix.linfty_opNorm_diagonal]
  simp [Pi.norm_def]

/-- **`‖exp x‖ ≤ exp ‖x‖`.**  Termwise from the exponential series: `‖(n!)⁻¹ • xⁿ‖ ≤ (n!)⁻¹‖x‖ⁿ`
by submultiplicativity for `n > 0` and by `norm_one_le` at `n = 0`, then compare the sums.

Note this bound alone does **not** give the decay `‖exp(tG)‖ → 0` for `G = Q − I`: it yields
`‖exp(tG)‖ ≤ exp(t‖G‖)`, which grows.  Decay needs the scalar-shift factorisation
`exp(t(Q−1)) = e^{−t}·exp(tQ)`, for which the missing ingredient is
`exp(c • 1) = (exp c) • 1` — see the file header. -/
theorem norm_exp_le {s : ℕ} (x : Matrix (Fin s) (Fin s) ℝ) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  rw [NormedSpace.exp_eq_tsum ℝ, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  have key : ∀ n : ℕ, ‖((n.factorial : ℝ)⁻¹) • x ^ n‖ ≤ ((n.factorial : ℝ)⁻¹) • ‖x‖ ^ n := by
    intro n
    rw [norm_smul, norm_inv, Real.norm_natCast, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using norm_one_le s
    · exact norm_pow_le' x hn
  have hs2 : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • ‖x‖ ^ n) := by
    have := Real.summable_pow_div_factorial ‖x‖
    simpa [smul_eq_mul, div_eq_inv_mul] using this
  have hs1 : Summable (fun n : ℕ => ‖((n.factorial : ℝ)⁻¹) • x ^ n‖) :=
    hs2.of_nonneg_of_le (fun n => norm_nonneg _) key
  exact (norm_tsum_le_tsum_norm hs1).trans (Summable.tsum_le_tsum key hs1 hs2)

/-! ## The scalar-shift factorisation and decay

`exp(t(Q−I)) = e^{−t}·exp(tQ)`, which is what converts the *growing* bound of `norm_exp_le` into
genuine decay.  Mathlib supplies the product rule for commuting arguments
(`NormedSpace.exp_add_of_commute`); the piece it lacks is `exp(c•1) = (exp c)•1`, proved here by
pulling the scalar out of the exponential series. -/

/-- **`exp(c • 1) = (exp c) • 1`.**  Since `(c•1)ⁿ = cⁿ•1`, the exponential series collapses onto
the scalar series.  Mathlib has no `NormedSpace.exp_algebraMap`, so this is proved directly using
`Summable.tsum_smul_const`. -/
theorem exp_smul_one (s : ℕ) (c : ℝ) :
    NormedSpace.exp (c • (1 : Matrix (Fin s) (Fin s) ℝ))
      = Real.exp c • (1 : Matrix (Fin s) (Fin s) ℝ) := by
  rw [NormedSpace.exp_eq_tsum ℝ, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  simp only []
  have hcongr : ∀ n : ℕ, ((n.factorial : ℝ)⁻¹) • (c • (1 : Matrix (Fin s) (Fin s) ℝ)) ^ n
      = (((n.factorial : ℝ)⁻¹ * c ^ n)) • (1 : Matrix (Fin s) (Fin s) ℝ) := by
    intro n; rw [smul_pow, one_pow, smul_smul]
  have hsum : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹ * c ^ n)) := by
    have := Real.summable_pow_div_factorial c
    simpa [div_eq_inv_mul] using this
  calc ∑' (n : ℕ), ((n.factorial : ℝ)⁻¹) • (c • (1 : Matrix (Fin s) (Fin s) ℝ)) ^ n
      = ∑' (n : ℕ), (((n.factorial : ℝ)⁻¹ * c ^ n)) • (1 : Matrix (Fin s) (Fin s) ℝ) :=
        tsum_congr hcongr
    _ = (∑' (n : ℕ), ((n.factorial : ℝ)⁻¹ * c ^ n)) • (1 : Matrix (Fin s) (Fin s) ℝ) :=
        hsum.tsum_smul_const _
    _ = (∑' (n : ℕ), ((n.factorial : ℝ)⁻¹) • c ^ n) • (1 : Matrix (Fin s) (Fin s) ℝ) := by
        congr 1

/-- **The scalar-shift factorisation.**  `exp(t•(Q−1)) = e^{−t} • exp(t•Q)`, since `t•Q` and
`(−t)•1` commute. -/
theorem exp_smul_sub_one {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (t : ℝ) :
    NormedSpace.exp (t • (Q - 1)) = Real.exp (-t) • NormedSpace.exp (t • Q) := by
  have hcomm : Commute (t • Q) ((-t) • (1 : Matrix (Fin s) (Fin s) ℝ)) :=
    (Commute.one_right (t • Q)).smul_right (-t)
  calc NormedSpace.exp (t • (Q - 1))
      = NormedSpace.exp ((t • Q) + ((-t) • (1 : Matrix (Fin s) (Fin s) ℝ))) := by
        congr 1; rw [smul_sub, sub_eq_add_neg, neg_smul]
    _ = NormedSpace.exp (t • Q) * NormedSpace.exp ((-t) • (1 : Matrix (Fin s) (Fin s) ℝ)) :=
        NormedSpace.exp_add_of_commute hcomm
    _ = NormedSpace.exp (t • Q) * (Real.exp (-t) • (1 : Matrix (Fin s) (Fin s) ℝ)) := by
        rw [exp_smul_one]
    _ = Real.exp (-t) • NormedSpace.exp (t • Q) := by rw [mul_smul_comm, mul_one]

/-- **The decay bound.**  For `t ≥ 0` and `‖Q‖ ≤ θ`,
`‖exp(t•(Q−1))‖ ≤ exp(−t(1−θ))`.  With `θ < 1` the right side tends to `0`. -/
theorem norm_exp_smul_sub_one_le {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ t : ℝ)
    (hQ : ‖Q‖ ≤ θ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • (Q - 1))‖ ≤ Real.exp (-(t * (1 - θ))) := by
  rw [exp_smul_sub_one, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 : ‖NormedSpace.exp (t • Q)‖ ≤ Real.exp (t * θ) := by
    refine (norm_exp_le _).trans ?_
    refine Real.exp_le_exp.mpr ?_
    calc ‖t • Q‖ = |t| * ‖Q‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = t * ‖Q‖ := by rw [abs_of_nonneg ht]
      _ ≤ t * θ := mul_le_mul_of_nonneg_left hQ ht
  calc Real.exp (-t) * ‖NormedSpace.exp (t • Q)‖
      ≤ Real.exp (-t) * Real.exp (t * θ) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp (-(t * (1 - θ))) := by rw [← Real.exp_add]; ring_nf

/-- **The decay itself.**  `exp(−t(1−θ)) → 0` as `t → ∞`, when `θ < 1`. -/
theorem tendsto_exp_decay (θ : ℝ) (hθ : θ < 1) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-(t * (1 - θ)))) Filter.atTop (nhds 0) := by
  have ha : (0:ℝ) < 1 - θ := by linarith
  have h : Filter.Tendsto (fun t : ℝ => -(t * (1 - θ))) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp (Filter.Tendsto.atTop_mul_const ha Filter.tendsto_id)
  exact Real.tendsto_exp_atBot.comp h

/-! ## Assembling the first moment

The three inputs to FTC-2 on a ray are now in place: the antiderivative
(`hasDerivAt_survival_antiderivative`), the decay of the antiderivative at `+∞`
(`tendsto_survival_zero`), and integrability of the integrand (`integrableOn_survival`).
`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` then gives the first moment identity. -/

/-- **The scalar decay.**  `(exp(t(Q−1))·y)ᵢ → 0` as `t → ∞`, by squeezing against the
operator-norm bound `‖exp(t(Q−1))‖·‖y‖ ≤ exp(−t(1−θ))·‖y‖`. -/
theorem tendsto_survival_zero {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ‖Q‖ ≤ θ) (hθ : θ < 1) (y : Fin s → ℝ) (i : Fin s) :
    Filter.Tendsto (fun t : ℝ => ((NormedSpace.exp (t • (Q - 1))).mulVec y) i)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ᶠ t : ℝ in Filter.atTop,
      ‖((NormedSpace.exp (t • (Q - 1))).mulVec y) i‖ ≤ Real.exp (-(t * (1 - θ))) * ‖y‖ := by
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with t ht
    calc ‖((NormedSpace.exp (t • (Q - 1))).mulVec y) i‖
        ≤ ‖(NormedSpace.exp (t • (Q - 1))).mulVec y‖ := norm_le_pi_norm _ i
      _ ≤ ‖NormedSpace.exp (t • (Q - 1))‖ * ‖y‖ := Matrix.linfty_opNorm_mulVec _ y
      _ ≤ Real.exp (-(t * (1 - θ))) * ‖y‖ :=
          mul_le_mul_of_nonneg_right (norm_exp_smul_sub_one_le Q θ t hQ ht) (norm_nonneg _)
  have hlim : Filter.Tendsto (fun t : ℝ => Real.exp (-(t * (1 - θ))) * ‖y‖)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_exp_decay θ hθ).mul_const ‖y‖
  exact squeeze_zero_norm' hbound hlim

/-- **Integrability on the ray.**  The integrand is continuous and dominated by
`exp(−(1−θ)t)·‖y‖`, which is integrable on `(0,∞)` for `θ < 1`. -/
theorem integrableOn_survival {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ‖Q‖ ≤ θ) (hθ : θ < 1) (y : Fin s → ℝ) (i : Fin s) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => ((NormedSpace.exp (t • (Q - 1))).mulVec y) i)
      (Set.Ioi 0) MeasureTheory.volume := by
  have hcont : Continuous (fun t : ℝ => ((NormedSpace.exp (t • (Q - 1))).mulVec y) i) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_mulVec_exp (Q - 1) y i t).continuousAt
  have h1θ : (0:ℝ) < 1 - θ := by linarith
  have hdom : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-(1-θ) * t) * ‖y‖) (Set.Ioi 0) MeasureTheory.volume :=
    (exp_neg_integrableOn_Ioi 0 h1θ).mul_const _
  refine MeasureTheory.Integrable.mono' hdom hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0:ℝ) ≤ t := le_of_lt ht
  calc ‖((NormedSpace.exp (t • (Q - 1))).mulVec y) i‖
      ≤ ‖(NormedSpace.exp (t • (Q - 1))).mulVec y‖ := norm_le_pi_norm _ i
    _ ≤ ‖NormedSpace.exp (t • (Q - 1))‖ * ‖y‖ := Matrix.linfty_opNorm_mulVec _ y
    _ ≤ Real.exp (-(t * (1 - θ))) * ‖y‖ :=
        mul_le_mul_of_nonneg_right (norm_exp_smul_sub_one_le Q θ t hQ ht0) (norm_nonneg _)
    _ = Real.exp (-(1-θ) * t) * ‖y‖ := by rw [show -(t * (1 - θ)) = -(1-θ)*t by ring]

/-- **The first moment identity.**

```
  ∫₀^∞ (exp(t(Q−I))·𝟙)ᵢ dt = ((I−Q)⁻¹·𝟙)ᵢ = (N𝟙)ᵢ .
```

This is the first half of the phase-type moment dictionary, *proved* rather than assumed: given
that the survival function of the absorption time is `t ↦ (exp(t(Q−I))𝟙)ᵢ`, the mean
`E_i[X] = ∫₀^∞P_i(X>t)dt` equals `(N𝟙)ᵢ`. -/
theorem integral_survival {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hu : IsUnit (1 - Q)) (hQ : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    (∫ t in Set.Ioi (0:ℝ), ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => 1)) i)
      = ((1 - Q)⁻¹.mulVec (fun _ => 1)) i := by
  set y := (1 - Q)⁻¹.mulVec (fun _ => (1:ℝ)) with hy
  set F := fun t : ℝ => ((NormedSpace.exp (t • (Q - 1))).mulVec y) i with hF
  have hderiv : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt F
      (-(((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i)) t :=
    fun t _ => hasDerivAt_survival_antiderivative Q hu i t
  have hcont : ContinuousWithinAt F (Set.Ici 0) 0 :=
    ((hasDerivAt_survival_antiderivative Q hu i 0).continuousAt).continuousWithinAt
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => -(((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i))
      (Set.Ioi 0) MeasureTheory.volume :=
    (integrableOn_survival Q θ hQ hθ (fun _ => (1:ℝ)) i).neg
  have hlim : Filter.Tendsto F Filter.atTop (nhds 0) :=
    tendsto_survival_zero Q θ hQ hθ y i
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hF0 : F 0 = y i := by simp [hF, NormedSpace.exp_zero, Matrix.one_mulVec]
  rw [MeasureTheory.integral_neg, hF0] at hftc
  linarith [hftc]

/-! ## The general form, and the second moment

`integral_survival` generalises: replacing `𝟙` by any `y` and `N𝟙` by `Ny`, the same
antiderivative argument gives `∫₀^∞(exp(t(Q−I))y)ᵢ dt = (Ny)ᵢ`.  Taking `y := N𝟙` then yields
`(N²𝟙)ᵢ` with no extra analysis. -/

/-- **The antiderivative property, for a general vector.**  `F(t) = (exp(tG)·Ny)ᵢ` has derivative
`−(exp(tG)·y)ᵢ`. -/
theorem hasDerivAt_antiderivative_gen {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hu : IsUnit (1 - Q)) (y : Fin s → ℝ) (i : Fin s) (t : ℝ) :
    HasDerivAt (fun u => ((NormedSpace.exp (u • (Q - 1))).mulVec ((1 - Q)⁻¹.mulVec y)) i)
      (-(((NormedSpace.exp (t • (Q - 1))).mulVec y) i)) t := by
  have h := hasDerivAt_mulVec_exp (Q - 1) ((1 - Q)⁻¹.mulVec y) i t
  convert h using 1
  rw [Matrix.mulVec_mulVec, mul_assoc, mul_inv_eq_neg_one Q hu, mul_neg, mul_one]
  simp [Matrix.neg_mulVec]

/-- **The resolvent integral, general form.**

```
  ∫₀^∞ (exp(t(Q−I))·y)ᵢ dt = ((I−Q)⁻¹·y)ᵢ .
```

With `y = 𝟙` this is the first moment; with `y = N𝟙` it is `(N²𝟙)ᵢ`, i.e. half the second
moment. -/
theorem integral_resolvent {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hu : IsUnit (1 - Q)) (hQ : ‖Q‖ ≤ θ) (hθ : θ < 1) (y : Fin s → ℝ) (i : Fin s) :
    (∫ t in Set.Ioi (0:ℝ), ((NormedSpace.exp (t • (Q - 1))).mulVec y) i)
      = ((1 - Q)⁻¹.mulVec y) i := by
  set z := (1 - Q)⁻¹.mulVec y with hz
  set F := fun t : ℝ => ((NormedSpace.exp (t • (Q - 1))).mulVec z) i with hF
  have hderiv : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt F
      (-(((NormedSpace.exp (t • (Q - 1))).mulVec y) i)) t :=
    fun t _ => hasDerivAt_antiderivative_gen Q hu y i t
  have hcont : ContinuousWithinAt F (Set.Ici 0) 0 :=
    ((hasDerivAt_antiderivative_gen Q hu y i 0).continuousAt).continuousWithinAt
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => -(((NormedSpace.exp (t • (Q - 1))).mulVec y) i))
      (Set.Ioi 0) MeasureTheory.volume :=
    (integrableOn_survival Q θ hQ hθ y i).neg
  have hlim : Filter.Tendsto F Filter.atTop (nhds 0) :=
    tendsto_survival_zero Q θ hQ hθ z i
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hF0 : F 0 = z i := by simp [hF, NormedSpace.exp_zero, Matrix.one_mulVec]
  rw [MeasureTheory.integral_neg, hF0] at hftc
  linarith [hftc]

/-- **The second moment identity.**

```
  ∫₀^∞ (exp(t(Q−I))·N𝟙)ᵢ dt = (N²𝟙)ᵢ ,
```

which is `E_i[X²]/2` for the phase-type absorption time.  Immediate from `integral_resolvent`
at `y := N𝟙`. -/
theorem integral_resolvent_sq {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hu : IsUnit (1 - Q)) (hQ : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    (∫ t in Set.Ioi (0:ℝ),
        ((NormedSpace.exp (t • (Q - 1))).mulVec ((1 - Q)⁻¹.mulVec (fun _ => 1))) i)
      = ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => 1))) i :=
  integral_resolvent Q θ hu hQ hθ _ i

end SSP.Semigroup
