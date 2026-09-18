import SSPLean.SemigroupMoments

/-!
# Positivity and monotonicity of the phase-type survival function

Toward building the absorption-time *law* rather than assuming it.  For substochastic `Q ≥ 0`,
the function

```
  surv(t) := (exp(t(Q−I))·𝟙)ᵢ
```

is nonnegative, equal to `1` at `t = 0`, nonincreasing, and tends to `0` (the last by
`SSP.Semigroup.tendsto_survival_zero`).  Hence `F(t) := 1 − surv(t)` is a genuine cumulative
distribution function, and `StieltjesFunction.measure` turns it into a probability measure on
`ℝ` — with no continuous-time Markov chain machinery.

The content here is the two structural facts: entrywise positivity of the matrix exponential,
and the sign of the derivative.
-/

open scoped Matrix.Norms.Operator
open NormedSpace Matrix SSP.Semigroup

set_option autoImplicit false

namespace SSP.Survival

/-- Powers of an entrywise-nonnegative matrix are entrywise nonnegative. -/
lemma pow_nonneg_entry {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (hQ : ∀ i j, 0 ≤ Q i j) :
    ∀ (n : ℕ) (i j : Fin s), 0 ≤ (Q ^ n) i j := by
  intro n
  induction n with
  | zero => intro i j; simp [Matrix.one_apply]; split <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hQ l j)

/-- **`exp(tQ) ≥ 0` entrywise** for `Q ≥ 0` and `t ≥ 0`.  Termwise from the exponential series:
every `(n!)⁻¹tⁿQⁿ` is entrywise nonnegative, and `tsum` preserves that.  The entry is extracted
by composing with `rowFun` at a basis vector, so `ContinuousLinearMap.map_tsum` applies. -/
theorem exp_nonneg_entry {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (t : ℝ) (ht : 0 ≤ t) (i j : Fin s) : 0 ≤ (NormedSpace.exp (t • Q)) i j := by
  have hsum : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (t • Q) ^ n) := by
    have h := NormedSpace.expSeries_summable (𝕂 := ℝ) (t • Q)
    exact h.congr fun n => by rw [NormedSpace.expSeries_apply_eq]
  have hmap := (rowFun (Pi.single j (1:ℝ)) i).map_tsum hsum
  have hentry : ∀ A : Matrix (Fin s) (Fin s) ℝ, rowFun (Pi.single j (1:ℝ)) i A = A i j := by
    intro A; rw [rowFun_apply]
    show (A.mulVec (Pi.single j (1:ℝ))) i = A i j
    simp [Matrix.mulVec_single]
  rw [NormedSpace.exp_eq_tsum ℝ]
  change 0 ≤ (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • (t • Q) ^ n) i j
  rw [← hentry (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • (t • Q) ^ n), hmap]
  refine tsum_nonneg fun n => ?_
  rw [hentry]
  have hrw : ((n.factorial : ℝ)⁻¹ • (t • Q) ^ n) i j
      = (n.factorial : ℝ)⁻¹ * (t ^ n * (Q ^ n) i j) := by
    rw [smul_pow, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [hrw]
  exact mul_nonneg (by positivity)
    (mul_nonneg (pow_nonneg ht n) (pow_nonneg_entry Q hQ n i j))

/-- **`exp(t(Q−I)) ≥ 0` entrywise**, via the scalar-shift factorisation
`exp(t(Q−1)) = e^{−t}·exp(tQ)`. -/
theorem exp_sub_one_nonneg_entry {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (t : ℝ) (ht : 0 ≤ t) (i j : Fin s) :
    0 ≤ (NormedSpace.exp (t • (Q - 1))) i j := by
  rw [exp_smul_sub_one, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (Real.exp_pos _).le (exp_nonneg_entry Q hQ t ht i j)

/-- If `M ≥ 0` entrywise and `v ≤ 0` pointwise then `(Mv)ᵢ ≤ 0`. -/
lemma mulVec_nonpos {s : ℕ} (M : Matrix (Fin s) (Fin s) ℝ) (v : Fin s → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ j, v j ≤ 0) (i : Fin s) : (M.mulVec v) i ≤ 0 := by
  change (∑ j, M i j * v j) ≤ 0
  refine Finset.sum_nonpos fun j _ => ?_
  exact mul_nonpos_of_nonneg_of_nonpos (hM i j) (hv j)

/-- **The generator applied to `𝟙` is nonpositive**: `((Q−I)𝟙)ⱼ = (Q𝟙)ⱼ − 1 ≤ 0` for
substochastic `Q`. -/
lemma sub_one_mulVec_one_nonpos {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hrow : ∀ i, ∑ j, Q i j ≤ 1) (j : Fin s) :
    ((Q - 1).mulVec (fun _ => (1:ℝ))) j ≤ 0 := by
  have hexp : ((Q - 1).mulVec (fun _ => (1:ℝ))) j = (∑ l, Q j l) - 1 := by
    change (∑ l, (Q - 1) j l * 1) = _
    simp only [mul_one, Matrix.sub_apply]
    rw [Finset.sum_sub_distrib]
    congr 1
    change (∑ l, (1 : Matrix (Fin s) (Fin s) ℝ) j l) = 1
    simp [Matrix.one_apply]
  rw [hexp]
  linarith [hrow j]

/-- **The survival function is nonincreasing.**  Its derivative is
`(exp(t(Q−I))·(Q−I)𝟙)ᵢ`, a nonnegative matrix applied to a nonpositive vector. -/
theorem survival_deriv_nonpos {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin s) :
    (((NormedSpace.exp (t • (Q - 1)) * (Q - 1)).mulVec (fun _ => (1:ℝ))) i) ≤ 0 := by
  rw [← Matrix.mulVec_mulVec]
  exact mulVec_nonpos _ _ (fun a b => exp_sub_one_nonneg_entry Q hQ t ht a b)
    (fun j => sub_one_mulVec_one_nonpos Q hrow j) i

/-! ## The survival function is a decreasing function from 1 to 0

Assembling: `surv` is continuous, `surv(0) = 1`, antitone on `[0,∞)`, nonnegative, and tends to
`0`.  So `F := 1 − surv` is a CDF on `[0,∞)`. -/

/-- **The survival function is antitone on `[0,∞)`.** -/
theorem survival_antitoneOn {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) (i : Fin s) :
    AntitoneOn (fun t : ℝ => ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i)
      (Set.Ici 0) := by
  set f := fun t : ℝ => ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i with hf
  have hderiv : ∀ t : ℝ, HasDerivAt f
      (((NormedSpace.exp (t • (Q - 1)) * (Q - 1)).mulVec (fun _ => (1:ℝ))) i) t :=
    fun t => hasDerivAt_mulVec_exp (Q - 1) (fun _ => (1:ℝ)) i t
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
  · exact (continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt).continuousOn
  · exact fun t _ => ((hderiv t).differentiableAt).differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    rw [(hderiv t).deriv]
    exact survival_deriv_nonpos Q hQ hrow t (le_of_lt ht) i

/-- **`surv(0) = 1`.**  No atom at the origin: absorption does not happen instantly. -/
theorem survival_at_zero {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (i : Fin s) :
    ((NormedSpace.exp ((0:ℝ) • (Q - 1))).mulVec (fun _ => (1:ℝ))) i = 1 := by
  simp [NormedSpace.exp_zero, Matrix.one_mulVec]

/-- **`surv ≥ 0`**, from entrywise positivity of the semigroup. -/
theorem survival_nonneg {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (t : ℝ) (ht : 0 ≤ t) (i : Fin s) :
    0 ≤ ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i := by
  change 0 ≤ ∑ j, (NormedSpace.exp (t • (Q - 1))) i j * 1
  refine Finset.sum_nonneg fun j _ => ?_
  rw [mul_one]
  exact exp_sub_one_nonneg_entry Q hQ t ht i j

/-- **The survival function has all four CDF properties.**  Packaged: with `F := 1 − surv`,
`F` is nondecreasing on `[0,∞)` (`survival_antitoneOn`), `F(0) = 0` (`survival_at_zero`),
`F ≤ 1` (`survival_nonneg`), and `F → 1` (`SSP.Semigroup.tendsto_survival_zero`).

That is exactly the input `StieltjesFunction.measure` needs to produce the absorption-time law,
so the remaining work is packaging rather than analysis. -/
theorem survival_cdf_properties {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    AntitoneOn (fun t : ℝ => ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i)
        (Set.Ici 0)
      ∧ ((NormedSpace.exp ((0:ℝ) • (Q - 1))).mulVec (fun _ => (1:ℝ))) i = 1
      ∧ (∀ t : ℝ, 0 ≤ t →
          0 ≤ ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i)
      ∧ Filter.Tendsto
          (fun t : ℝ => ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i)
          Filter.atTop (nhds 0) :=
  ⟨survival_antitoneOn Q hQ hrow i, survival_at_zero Q i,
   fun t ht => survival_nonneg Q hQ t ht i,
   SSP.Semigroup.tendsto_survival_zero Q θ hnorm hθ (fun _ => (1:ℝ)) i⟩

/-! ## The cumulative distribution function

`F(t) := 0` for `t ≤ 0`, `1 − surv(t)` for `t > 0`.  Since `surv(0) = 1`, the two branches agree
at the origin, so `F` glues continuously.  Monotonicity across the join is proved here; it is the
first of the two `StieltjesFunction` fields. -/

/-- **`surv ≤ 1` on `[0,∞)`**, from antitonicity together with `surv(0) = 1`. -/
theorem survival_le_one {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j ≤ 1) (i : Fin s) (t : ℝ) (ht : 0 ≤ t) :
    ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i ≤ 1 := by
  have h := survival_antitoneOn Q hQ hrow i (Set.mem_Ici.mpr (le_refl 0))
    (Set.mem_Ici.mpr ht) ht
  simp only [] at h
  calc ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i
      ≤ ((NormedSpace.exp ((0:ℝ) • (Q - 1))).mulVec (fun _ => (1:ℝ))) i := h
    _ = 1 := survival_at_zero Q i

/-- The candidate CDF of the absorption time started at `i`. -/
noncomputable def cdfF {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (i : Fin s) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else 1 - ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i

/-- **`F` is monotone on all of `ℝ`** — the first `StieltjesFunction` field.

Four cases.  Both arguments `≤ 0`: `F` is `0`.  Straddling the origin: `0 ≤ 1 − surv` because
`surv ≤ 1`.  Both `> 0`: antitonicity of `surv`.  The fourth is vacuous. -/
theorem cdfF_monotone {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j ≤ 1) (i : Fin s) : Monotone (cdfF Q i) := by
  intro a b hab
  unfold cdfF
  split_ifs with ha hb hb
  · exact le_refl 0
  · have hb' : (0:ℝ) ≤ b := le_of_lt (not_le.mp hb)
    linarith [survival_le_one Q hQ hrow i b hb']
  · exfalso
    have : (0:ℝ) < a := not_le.mp ha
    linarith
  · have ha' : (0:ℝ) ≤ a := le_of_lt (not_le.mp ha)
    have hb' : (0:ℝ) ≤ b := le_trans ha' hab
    have h := survival_antitoneOn Q hQ hrow i (Set.mem_Ici.mpr ha') (Set.mem_Ici.mpr hb') hab
    simp only [] at h
    linarith

/-- **`F(0) = 0`** and **`F → 1`**: the CDF's boundary behaviour.  The limit is
`SSP.Semigroup.tendsto_survival_zero` transported through `F = 1 − surv`. -/
theorem cdfF_at_zero {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (i : Fin s) :
    cdfF Q i 0 = 0 := by simp [cdfF]

/-- **`F` agrees with `1 − surv` on all of `[0,∞)`** — including at the origin, where the
`if`-branch gives `F(0) = 0` and `1 − surv(0) = 1 − 1 = 0`.  This exact gluing is what makes `F`
right-continuous at `0`. -/
theorem cdfF_eqOn_Ici {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (i : Fin s) :
    Set.EqOn (cdfF Q i)
      (fun t => 1 - ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i)
      (Set.Ici 0) := by
  intro t ht
  rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with h | h
  · subst h
    simp only [cdfF, if_pos (le_refl (0:ℝ))]
    rw [survival_at_zero Q i]; ring
  · simp only [cdfF, if_neg (not_le.mpr h)]

/-- **`F` is right-continuous everywhere** — the second `StieltjesFunction` field.

For `x < 0`, `F` vanishes on a neighbourhood.  For `x ≥ 0`, `Ici x ⊆ Ici 0` and `F` agrees there
with the continuous `1 − surv`; the `x = 0` case is covered because the agreement of
`cdfF_eqOn_Ici` includes the origin. -/
theorem cdfF_right_continuous {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (i : Fin s) (x : ℝ) :
    ContinuousWithinAt (cdfF Q i) (Set.Ici x) x := by
  have hcont : Continuous
      (fun t : ℝ => 1 - ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i) :=
    continuous_const.sub (continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_mulVec_exp (Q - 1) (fun _ => (1:ℝ)) i t).continuousAt)
  rcases lt_or_ge x 0 with hx | hx
  · have heq : ∀ᶠ t in nhdsWithin x (Set.Ici x), cdfF Q i t = 0 := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx)] with t ht
      simp [cdfF, le_of_lt (Set.mem_Iio.mp ht)]
    refine ContinuousWithinAt.congr_of_eventuallyEq continuousWithinAt_const heq ?_
    simp [cdfF, le_of_lt hx]
  · have hsub : Set.Ici x ⊆ Set.Ici (0:ℝ) := Set.Ici_subset_Ici.mpr hx
    refine ContinuousWithinAt.congr hcont.continuousWithinAt
      (fun t ht => cdfF_eqOn_Ici Q i (hsub ht)) ?_
    exact cdfF_eqOn_Ici Q i (Set.mem_Ici.mpr hx)

/-- **The absorption-time CDF as a `StieltjesFunction`.**

Both fields are now available, so `F` is a Stieltjes function and `StieltjesFunction.measure`
produces the law of the absorption time — with no continuous-time Markov chain construction. -/
noncomputable def survivalStieltjes {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) (i : Fin s) :
    StieltjesFunction ℝ where
  toFun := cdfF Q i
  mono' := cdfF_monotone Q hQ hrow i
  right_continuous' := cdfF_right_continuous Q i

/-! ## The absorption-time law is a probability measure

`StieltjesFunction.measure_univ` needs the two boundary limits.  `F → 0` at `−∞` is immediate
(`F` vanishes there); `F → 1` at `+∞` is `SSP.Semigroup.tendsto_survival_zero` transported
through `F = 1 − surv`. -/

/-- `F → 0` at `−∞`. -/
theorem cdfF_tendsto_atBot {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (i : Fin s) :
    Filter.Tendsto (cdfF Q i) Filter.atBot (nhds 0) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_le_atBot (0:ℝ)] with t ht
  simp [cdfF, ht]

/-- `F → 1` at `+∞`, since `surv → 0`. -/
theorem cdfF_tendsto_atTop {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    Filter.Tendsto (cdfF Q i) Filter.atTop (nhds 1) := by
  have hsurv := SSP.Semigroup.tendsto_survival_zero Q θ hnorm hθ (fun _ => (1:ℝ)) i
  have hlim : Filter.Tendsto
      (fun t : ℝ => 1 - ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i)
      Filter.atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hsurv
  rw [sub_zero] at hlim
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with t ht
  exact (cdfF_eqOn_Ici Q i (Set.mem_Ici.mpr ht)).symm

/-- **The absorption-time law has total mass `1`.** -/
theorem measure_univ_eq_one {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    (survivalStieltjes Q hQ hrow i).measure Set.univ = 1 := by
  rw [StieltjesFunction.measure_univ _ (cdfF_tendsto_atBot Q i)
    (cdfF_tendsto_atTop Q θ hnorm hθ i)]
  simp

/-- **The absorption-time law is a probability measure.**  Registered as an instance-shaped
statement so `MeasureTheory` lemmas requiring `IsProbabilityMeasure` apply. -/
theorem isProbabilityMeasure {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    MeasureTheory.IsProbabilityMeasure (survivalStieltjes Q hQ hrow i).measure :=
  ⟨measure_univ_eq_one Q θ hQ hrow hnorm hθ i⟩

/-- **The law is supported on `[0,∞)`**: it gives no mass to the negative half-line, since `F`
is constant there. -/
theorem measure_Iic_zero {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) (i : Fin s) :
    (survivalStieltjes Q hQ hrow i).measure (Set.Iic 0) = 0 := by
  rw [StieltjesFunction.measure_Iic _ (cdfF_tendsto_atBot Q i)]
  simp [survivalStieltjes, cdfF_at_zero]

end SSP.Survival
