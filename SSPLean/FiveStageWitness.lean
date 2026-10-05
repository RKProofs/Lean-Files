import Mathlib
import SSPLean.AlgStabCounterexample

/-!
# A five-stage counterexample, with a degree-6 parameter

`SSPLean/SixStageWitness.lean` refutes the algebraic-stability Claim of `main-4.tex` at six
stages, with a parameter of degree `3`.  This file records the analytic and arithmetic core
of a **five**-stage counterexample.  Five stages is one fewer than the fully formalized
witness, and — since a rank-`3` certificate is forced (`SSP.Counterexample.Six`'s rank
argument is independent of the stage count) while `rank R ≤ s` — it is close to the smallest
conceivable stage count for this mechanism.

## The construction

Let `P` be the cyclic shift on `range 5` and take the *symmetric* circulant

  `G = t·I + u·P + t·P²`,   `u = (1/2 − A t)/B`,  `A = (7−√5)/2`,  `B = (1+√5)/2`,

with `A = D⁻¹ G D`, `b = D h`, `R = D X D` as in the six-stage file.  The point is again a
three-dimensional invariant subspace on which everything is *algebraic of low degree*.  Here
`ℚ(ζ₅)` has degree `4`, so no rational invariant subspace exists — but rescaling the sine
basis vector by `sin(2π/5)` clears the irrationality: with

  `x = (1, c, −d, −d, c)`,   `w = (0, 1, 2c, −2c, −1)`,
  `c = (√5−1)/4`,  `d = (√5+1)/4`,

one has `P x = c·x − s·w` and `P w = x + c·w` with `s = (5+√5)/8`, and the Gram matrix is
`diag(5, 5/2, 5−√5)`.  Every structure constant lies in `ℚ(√5)`.

Exactly as at six stages, two order conditions are then *identities*:
`m₀ = 2·tr Γ = 3g₀ + φ·g₁ + (1−φ)·g₂` (so `m₀ = 1` is the single linear condition defining
`u` above), and `m₁ = m₀²/2 = 1/2`.  The third, `m₂ = bᵀAc`, is again **independent of `v`**,
so `m₂ = 1/6` is one equation in `g` alone; on the symmetric slice it is a *cubic* over
`ℚ(√5)`:

  `(325−145√5)t³ + (−90+40√5)t² + (35/4−15/4√5)t + (−1/8+1/8√5) = 1/6`.

Clearing denominators gives `U(t) + √5·V(t) = 0` with
`U = −7 + 210t − 2160t² + 7800t³` and `V = 3 − 90t + 960t² − 3480t³`, whence
`U² − 5V² = 4·(72000t⁶ − 72000t⁵ + 50400t⁴ − 12000t³ + 1260t² − 60t + 1)`: the parameter has
degree `6` over `ℚ`.

Only `bᵀc² = 1/3` is left, and it is obtained from a sign change along the rational line
`v(x) = (x, 1, 12/5, 21/20, 11/20)` between `x = 2/5` and `x = 21/50`.

## What is proved here

* `tau5_cubic` — the parameter exists, **as a root of the `ℚ(√5)`-cubic**, in a rational
  bracket of width `10⁻⁶`.  Taking it from the cubic rather than from the sextic matters: the
  sextic is the norm form, and its other real root `≈ 0.10362` satisfies the *conjugate*
  cubic (with `−√5`), not this one.
* `cubic_to_minpoly` — the cubic implies the sextic, via `U² − 5V² = 4·quin`.
* `cubic_reduce` — the cubic in the normalisation form `t³ = …`, which together with
  `r² = 5` reduces every polynomial in `(r, t)`.
* `tau5_exists`, `quin_lo`, `quin_hi` — the sextic also brackets the parameter (`quin` is
  decreasing there, while the cubic is increasing).
* `sqrt5_bracket`, `sqrt5_sq` — the rational bracket for `√5`.
* `bL`, `cL`, `bR`, `cR` — the tableau at the two endpoints, as explicit elements of
  `ℚ(√5, t)`; the abscissas are *linear* in `t`.
* `m0_L`, `m0_R` — `bᵀe = 1`, by `ring` alone (no reduction needed).
* `m1_L`, `m1_R` — `bᵀc = 1/2`, with explicit `linear_combination` certificates against
  `hr` and `ht3`.  The certificate is the *same* at both endpoints, reflecting that this
  condition holds identically along the line.
* `defect_L_eq`, `defect_R_eq` — **`dL` and `dR` are the order-three defect of the
  tableau**.  This is the identification that closes the earlier gap.
* `dL_pos`, `dR_neg` — the defect signs, decided by interval arithmetic on the two rational
  brackets alone.
* `tableau_defect_sign_change` — the sign change, stated **about the tableau itself**: at the
  cubic's root the defect is positive at `x = 2/5` and negative at `x = 21/50`.
* `defect5_sign_change`, `five_stage_defect_root` — the earlier, weaker forms, retained.

## The side conditions

* `g_pos` — the three circulant bands `g₀ = g₂ = t`, `g₁ = (r−1)/4 + (3−2r)t` are positive on
  the brackets, hence `G ≥ 0` and so `A = D⁻¹GD ≥ 0` for `v > 0`.
* `bL_pos`, `bR_pos` — `b > 0` at both endpoints.
* `cL_mem` — the abscissas lie strictly inside `(0,1)`.
* `perm5`, `cL_sorted`, `cR_sorted` — the abscissas are strictly ordered by the *fixed*
  permutation `(2,3,4,1,0)`, the same at both endpoints, hence pairwise distinct.
* `AL`, `RL` — the coefficient matrix and certificate at `x = 2/5`, over `ℚ(√5, t)`.
* `RL_symm`, `RL_rowsum` — `R` symmetric with `R e = b`.
* `m2_L`, `m2_R` — `bᵀAc = 1/6`.
* `Mzero_L_i_j` (15 lemmas) and `ML_zero` — **`M = R A + Aᵀ R − b bᵀ = 0`**, entrywise and in
  matrix form.
* `five_conditions_L` — ten of the eleven conditions, packaged.

## Positive semidefiniteness of `R`

Because `z = Bᵗv` is constant along the null-direction segment, the reduced matrix `S` is the
*same* at both endpoints, so a single proof serves both.  The chain is
`S ⪰ 0 → X = B S Bᵀ ⪰ 0 → R = D X D ⪰ 0`:

* `psd_of_minors`, `sos3` — Sylvester made explicit, for an *abstract* symmetric `3 × 3` form.
  Proving the completion of squares abstractly and instantiating avoids `ring` blowing up on
  the size of the literals, which it does if `Sm5` is unfolded inside the identity.
* `sm5_1_pos`, `sm5_2_pos`, `sm5_3_pos` — the leading principal minors of `S` are positive on
  the two brackets, by interval arithmetic.
* `sm5_2_eq`, `sm5_3_eq` — the stored (pre-reduced) minors agree with the raw expressions
  `S₀₀S₁₁ − S₀₁²` and `det S`, whose `t`-degrees are `4` and `6`; matched by
  `linear_combination` against `hr` and `ht3`.
* `Sm5_psd` — hence the form of `S` is nonnegative.
* `quadform_transfer` — the abstract identity `xᵗ(BSBᵀ)x = (Bᵗx)ᵗS(Bᵗx)`, proved by expanding
  the concrete ranges `5` and `3`.
* `Xm5_eq`, `Xm5_psd` — `X = B S Bᵀ` entrywise and its positive semidefiniteness.
* `RL_eq_DXD`, `RL_psd` — `R = D X D` and **`R ⪰ 0`**.

`five_conditions_L` now carries all eleven of the Claim's structural conditions at `x = 2/5`
(everything except `bᵀc² = 1/3`, which fails there by design — that is what the sign change
supplies).

## What is NOT proved here

The conditions are established at the two *endpoints* of the segment, `s = 0` and
`s = −1/50`, not at the interior `s*` where `bᵀc² = 1/3`.  The three moment conditions and
`R ⪰ 0` do transfer, since `z` — hence `S`, `h`, `X` — is constant in `s`; what does not yet
transfer is the positivity data (`b > 0`, `c ⊂ (0,1)`, the ordering) and `M = 0`, each of which
is currently proved only at the endpoints.  Doing that needs `b`, `c`, `A`, `R` as explicit
functions of `s` — mechanical, but a substantial extension of what is here.

So there is still no five-stage analogue of `SSP.Counterexample.Six.claim_is_false`, and the
complete machine-checked refutation remains the six-stage one.
-/

open Finset

namespace SSP

namespace Counterexample

namespace Five

/-! ## The parameter -/

/-- The degree-6 minimal polynomial of the five-stage parameter. -/
noncomputable def quin (x : ℝ) : ℝ :=
  72000*x^6 - 72000*x^5 + 50400*x^4 - 12000*x^3 + 1260*x^2 - 60*x + 1

lemma quin_continuous : Continuous quin := by unfold quin; fun_prop

lemma quin_lo : 0 < quin (35127/1000000) := by unfold quin; norm_num

lemma quin_hi : quin (35128/1000000) < 0 := by unfold quin; norm_num

/-- **The five-stage parameter exists**, in a bracket of width `10⁻⁶`.  Every sign assertion
below is decided from this bracket and the one for `√5`. -/
theorem tau5_exists :
    ∃ t : ℝ, t ∈ Set.Ioo (35127/1000000 : ℝ) (35128/1000000) ∧ quin t = 0 := by
  have h : (0:ℝ) ∈ Set.Ioo (quin (35128/1000000)) (quin (35127/1000000)) :=
    Set.mem_Ioo.2 ⟨quin_hi, quin_lo⟩
  obtain ⟨t, ht, h0⟩ :=
    intermediate_value_Ioo' (by norm_num : (35127/1000000:ℝ) ≤ 35128/1000000)
      quin_continuous.continuousOn h
  exact ⟨t, ht, h0⟩

/-- **The `ℚ(√5)`-cubic implies the `ℚ`-sextic.**  With `r² = 5`, writing the cubic as
`U(t) + r·V(t) = 0` gives `U² − 5V² = 0`, and `U² − 5V² = 4·quin`. -/
theorem cubic_to_minpoly (r t : ℝ) (hr : r^2 = 5)
    (hcub : (325-145*r)*t^3 + (-90+40*r)*t^2 + (35/4-15/4*r)*t + (-1/8+1/8*r) = 1/6) :
    quin t = 0 := by
  have hUV : (-7 + 210*t - 2160*t^2 + 7800*t^3)
      + r*(3 - 90*t + 960*t^2 - 3480*t^3) = 0 := by
    linear_combination 24 * hcub
  unfold quin
  linear_combination
    ((-7 + 210*t - 2160*t^2 + 7800*t^3) - r*(3 - 90*t + 960*t^2 - 3480*t^3))/4 * hUV
      + (3 - 90*t + 960*t^2 - 3480*t^3)^2/4 * hr

/-! ## The rational bracket for `√5` -/

lemma sqrt5_sq : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)

lemma sqrt5_bracket :
    Real.sqrt 5 ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000) := by
  constructor
  · rw [show (2236067/1000000 : ℝ) = Real.sqrt ((2236067/1000000)^2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  · rw [show (2236068/1000000 : ℝ) = Real.sqrt ((2236068/1000000)^2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)

/-! ## The order-three defect at the two endpoints

Along the rational line `v(x) = (x, 1, 12/5, 21/20, 11/20)` the vector `z = Bᵀv` varies, so
unlike the six-stage family the certificate is not constant here; what matters is only that
the defect changes sign, which the two explicit elements of `ℚ(√5, t)` below exhibit. -/

/-- The order-three defect at `x = 2/5`, as an element of `ℚ(√5, t)`. -/
noncomputable def dL (r t : ℝ) : ℝ :=
  (252809463259/1944530945280 - 2156967055/64817698176*r)
  + (-76076274451/6173114112 + 1038497073091/216058993920*r)*t
  + (30955193849/300081936 - 23231220604/506388267*r)*t^2

/-- The order-three defect at `x = 21/50`. -/
noncomputable def dR (r t : ℝ) : ℝ :=
  (-11538008790975647/3665254263282057600 + 8651548803324377/366525426328205760*r)
  + (-473145162279101269/48870056843760768 + 4439303432633995231/1221751421094019200*r)*t
  + (226480195552013899/2545315460612540 - 100646432317036741/2545315460612540*r)*t^2

/-- The defect at `x = 2/5` is positive, for any `r`, `t` in the two brackets. -/
lemma dL_pos {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) : 0 < dL r t := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  unfold dL
  nlinarith [ht1, ht2, hr1, hr2, mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hr1),
    sq_nonneg t, sq_nonneg (t - 35127/1000000), sq_nonneg (r - 2236067/1000000)]

/-- The defect at `x = 21/50` is negative, for any `r`, `t` in the two brackets. -/
lemma dR_neg {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) : dR r t < 0 := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  unfold dR
  nlinarith [ht1, ht2, hr1, hr2, mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hr1),
    sq_nonneg t, sq_nonneg (t - 35127/1000000), sq_nonneg (r - 2236067/1000000)]

/-- The `ℚ(√5)`-cubic, as a function of `t` with `r = √5` substituted. -/
noncomputable def cub5 (t : ℝ) : ℝ :=
  (325-145*Real.sqrt 5)*t^3 + (-90+40*Real.sqrt 5)*t^2
    + (35/4-15/4*Real.sqrt 5)*t + (-1/8+1/8*Real.sqrt 5) - 1/6

lemma cub5_cont : Continuous cub5 := by unfold cub5; fun_prop

lemma cub5_lo : cub5 (35127/1000000) < 0 := by
  unfold cub5
  obtain ⟨h1, h2⟩ := sqrt5_bracket
  nlinarith [h1, h2]

lemma cub5_hi : 0 < cub5 (35128/1000000) := by
  unfold cub5
  obtain ⟨h1, h2⟩ := sqrt5_bracket
  nlinarith [h1, h2]

/-- **The parameter, from the cubic itself.** -/
theorem tau5_cubic :
    ∃ t : ℝ, t ∈ Set.Ioo (35127/1000000 : ℝ) (35128/1000000)
      ∧ (325-145*Real.sqrt 5)*t^3 + (-90+40*Real.sqrt 5)*t^2
        + (35/4-15/4*Real.sqrt 5)*t + (-1/8+1/8*Real.sqrt 5) = 1/6 := by
  have h : (0:ℝ) ∈ Set.Ioo (cub5 (35127/1000000)) (cub5 (35128/1000000)) :=
    Set.mem_Ioo.2 ⟨cub5_lo, cub5_hi⟩
  obtain ⟨t, ht, h0⟩ :=
    intermediate_value_Ioo (by norm_num : (35127/1000000:ℝ) ≤ 35128/1000000)
      cub5_cont.continuousOn h
  refine ⟨t, ht, ?_⟩
  unfold cub5 at h0
  linarith

/-! ## The tableau, and the defect identified

The construction is `A = D⁻¹GD`, `b = Dh`, `R = DXD` with `D = diag v(x)` along the rational
line `v(x) = (x, 1, 12/5, 21/20, 11/20)`.  At each endpoint the resulting `b` and `c` are
explicit elements of `ℚ(√5, t)`, listed below; the abscissas are *linear* in `t`.

Every identity here is a polynomial identity in the two free reals `r`, `t`, closed by
`linear_combination` with explicit certificates against the two reduction hypotheses
`hr : r² = 5` and `ht3 : t³ = …` (the latter is `cubic_reduce` applied to the cubic). -/

/-- The cubic in the reduction form `t³ = …` used to normalise polynomials in `t`. -/
lemma cubic_reduce (r t : ℝ) (hr : r^2 = 5)
    (hcub : (325-145*r)*t^3 + (-90+40*r)*t^2 + (35/4-15/4*r)*t + (-1/8+1/8*r) = 1/6) :
    t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300) := by
  linear_combination ((325+145*r)/500) * hcub
    + ((841/20)*t^3 - (58/5)*t^2 + (87/80)*t - (29/800)) * hr

/-! ### The tableau at `x = 2/5` -/

/-- Weights at `x = 2/5`. -/
noncomputable def bL (r t : ℝ) : ℕ → ℝ := fun i =>
  match i with
  | 0 => (((3599093/2192157 : ℝ) + (-1435777/2192157 : ℝ)*r) + ((-75824660/2192157 : ℝ) + (3733888/243573 : ℝ)*r)*t + ((172876640/730719 : ℝ) + (-77100160/730719 : ℝ)*r)*t^2)
  | 1 => (((28818685/4384314 : ℝ) + (-12119345/4384314 : ℝ)*r) + ((-285444050/2192157 : ℝ) + (14174200/243573 : ℝ)*r)*t + ((496916000/730719 : ℝ) + (-221921200/730719 : ℝ)*r)*t^2)
  | 2 => (((-12459758/730719 : ℝ) + (5671030/730719 : ℝ)*r) + ((270451400/730719 : ℝ) + (-13407376/81191 : ℝ)*r)*t + ((-510073280/243573 : ℝ) + (227981440/243573 : ℝ)*r)*t^2)
  | 3 => (((75255215/5845752 : ℝ) + (-33620251/5845752 : ℝ)*r) + ((-401666615/1461438 : ℝ) + (9977576/81191 : ℝ)*r)*t + ((396263980/243573 : ℝ) + (-177294320/243573 : ℝ)*r)*t^2)
  | 4 => (((-4841971/1594296 : ℝ) + (2247239/1594296 : ℝ)*r) + ((27711715/398574 : ℝ) + (-692608/22143 : ℝ)*r)*t + ((-29851340/66429 : ℝ) + (13360000/66429 : ℝ)*r)*t^2)
  | _ => 0

/-- Abscissas at `x = 2/5` (linear in `t`). -/
noncomputable def cL (r t : ℝ) : ℕ → ℝ := fun i =>
  match i with
  | 0 => (((-5/8 : ℝ) + (5/8 : ℝ)*r) + ((29/2 : ℝ) + (-5 : ℝ)*r)*t)
  | 1 => (((-3/5 : ℝ) + (3/5 : ℝ)*r) + ((37/4 : ℝ) + (-24/5 : ℝ)*r)*t)
  | 2 => (((-7/64 : ℝ) + (7/64 : ℝ)*r) + ((61/24 : ℝ) + (-7/8 : ℝ)*r)*t)
  | 3 => (((-11/84 : ℝ) + (11/84 : ℝ)*r) + ((62/21 : ℝ) + (-22/21 : ℝ)*r)*t)
  | 4 => (((-2/11 : ℝ) + (2/11 : ℝ)*r) + ((5 : ℝ) + (-16/11 : ℝ)*r)*t)
  | _ => 0

/-- `bᵀe = 1` at `x = 2/5`. -/
lemma m0_L (r t : ℝ) : ∑ i ∈ range 5, bL r t i = 1 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bL]
  ring

/-- `bᵀc = 1/2` at `x = 2/5`. -/
lemma m1_L (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∑ i ∈ range 5, bL r t i * cL r t i = 1/2 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bL, cL]
  linear_combination ((-10683/440 : ℝ) + (32009/44 : ℝ)*t + (-12938/11 : ℝ)*t^2 + (18000/11 : ℝ)*t^3) * hr + ((166500/11 : ℝ) + (-74460/11 : ℝ)*r) * ht3

/-- **`dL` is the order-three defect of the tableau at `x = 2/5`.** -/
lemma defect_L_eq (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ i ∈ range 5, bL r t i * (cL r t i)^2) - 1/3 = dL r t := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bL, cL, dL]
  linear_combination ((4265667749065861/77781237811200 : ℝ) + (-992858095784717/432117987840 : ℝ)*t + (105142395963625/4629835584 : ℝ)*t^2 + (-23765068235503/578729448 : ℝ)*t^3 + (3403851599315/56265363 : ℝ)*t^4 + (-6275183961709/5185415854080 : ℝ)*r + (29425950333713/648176981760 : ℝ)*r*t + (-1618424410562/2531941335 : ℝ)*r*t^2 + (2693469808111/675184356 : ℝ)*r*t^3 + (-1568430980758/168796089 : ℝ)*r*t^4) * hr + ((-134498340782305/4051106136 : ℝ) + (67489361201380/168796089 : ℝ)*t + (30077945254487/2025553068 : ℝ)*r + (-10060478730305/56265363 : ℝ)*r*t) * ht3

/-! ### The tableau at `x = 21/50` -/

/-- Weights at `x = 21/50`. -/
noncomputable def bR (r t : ℝ) : ℕ → ℝ := fun i =>
  match i with
  | 0 => (((5413499174097/3305604494302 : ℝ) + (-2145127670805/3305604494302 : ℝ)*r) + ((-56959082019000/1652802247151 : ℝ) + (25231185228270/1652802247151 : ℝ)*r)*t + ((392440442398200/1652802247151 : ℝ) + (-174997079346600/1652802247151 : ℝ)*r)*t^2)
  | 1 => (((11110479185275/1652802247151 : ℝ) + (-4679329519075/1652802247151 : ℝ)*r) + ((-220628971170000/1652802247151 : ℝ) + (98606737355700/1652802247151 : ℝ)*r)*t + ((1157766173472000/1652802247151 : ℝ) + (-517077832116000/1652802247151 : ℝ)*r)*t^2)
  | 2 => (((-28432634841900/1652802247151 : ℝ) + (12934348642620/1652802247151 : ℝ)*r) + ((617339177826000/1652802247151 : ℝ) + (-275431873187040/1652802247151 : ℝ)*r)*t + ((-3500776644494400/1652802247151 : ℝ) + (1564689181003200/1652802247151 : ℝ)*r)*t^2)
  | 3 => (((84577669356495/6611208988604 : ℝ) + (-37792053077415/6611208988604 : ℝ)*r) + ((-451620846890850/1652802247151 : ℝ) + (201931858712955/1652802247151 : ℝ)*r)*t + ((2676187074966300/1652802247151 : ℝ) + (-1197373210217100/1652802247151 : ℝ)*r)*t^2)
  | 4 => (((-1773166917235/601018998964 : ℝ) + (823839265895/601018998964 : ℝ)*r) + ((10169974750350/150254749741 : ℝ) + (-4576173464535/150254749741 : ℝ)*r)*t + ((-65965186031100/150254749741 : ℝ) + (29523540061500/150254749741 : ℝ)*r)*t^2)
  | _ => 0

/-- Abscissas at `x = 21/50` (linear in `t`). -/
noncomputable def cR (r t : ℝ) : ℕ → ℝ := fun i =>
  match i with
  | 0 => (((-25/42 : ℝ) + (25/42 : ℝ)*r) + ((97/7 : ℝ) + (-100/21 : ℝ)*r)*t)
  | 1 => (((-3/5 : ℝ) + (3/5 : ℝ)*r) + ((37/4 : ℝ) + (-24/5 : ℝ)*r)*t)
  | 2 => (((-7/64 : ℝ) + (7/64 : ℝ)*r) + ((61/24 : ℝ) + (-7/8 : ℝ)*r)*t)
  | 3 => (((-11/84 : ℝ) + (11/84 : ℝ)*r) + ((104/35 : ℝ) + (-22/21 : ℝ)*r)*t)
  | 4 => (((-21/110 : ℝ) + (21/110 : ℝ)*r) + ((281/55 : ℝ) + (-84/55 : ℝ)*r)*t)
  | _ => 0

/-- `bᵀe = 1` at `x = 21/50`. -/
lemma m0_R (r t : ℝ) : ∑ i ∈ range 5, bR r t i = 1 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bR]
  ring

/-- `bᵀc = 1/2` at `x = 21/50`. -/
lemma m1_R (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∑ i ∈ range 5, bR r t i * cR r t i = 1/2 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bR, cR]
  linear_combination ((-10683/440 : ℝ) + (32009/44 : ℝ)*t + (-12938/11 : ℝ)*t^2 + (18000/11 : ℝ)*t^3) * hr + ((166500/11 : ℝ) + (-74460/11 : ℝ)*r) * ht3

/-- **`dR` is the order-three defect of the tableau at `x = 21/50`.** -/
lemma defect_R_eq (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ i ∈ range 5, bR r t i * (cR r t i)^2) - 1/3 = dR r t := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bR, cR, dR]
  linear_combination ((8025986092456359782999/146610170531282304000 : ℝ) + (-797164082031700959947/349071834598291200 : ℝ)*t + (4554255173373458351541/203625236849003200 : ℝ)*t^2 + (-77280022517249622871/1908986595459405 : ℝ)*t^3 + (7590379877845149597/127265773030627 : ℝ)*t^4 + (-2352776774980507699/1954802273750430720 : ℝ)*r + (3676286966609192163/81450094739601280 : ℝ)*r*t + (-25866703888577258933/40725047369800640 : ℝ)*r*t^2 + (30249160466610379457/7635946381837620 : ℝ)*r*t^3 + (-1173503051125150485/127265773030627 : ℝ)*r*t^4) * hr + ((-1205583773313375839/36361649437322 : ℝ) + (50001716512451080408/127265773030627 : ℝ)*t + (113234011229211447041/7635946381837620 : ℝ)*r + (-22360912409830905938/127265773030627 : ℝ)*r*t) * ht3
/-! ## The algebraic side conditions at `x = 2/5`

The construction is `A = D⁻¹GD`, `R = DXD`.  Below `AL` and `RL` are those matrices at the
left endpoint, as explicit elements of `ℚ(√5, t)`; `G` is circulant of bandwidth `3`, so `AL`
has fifteen nonzero entries.  All identities are closed by `linear_combination` against
`hr : r² = 5` and `ht3` (from `cubic_reduce`), with certificates computed by eliminating
`r^{≥2}` and `t^{≥3}` to a fixed point. -/



/-- The circulant bands `g₀ = g₂ = t`, `g₁ = (r−1)/4 + (3−2r)t`. -/
noncomputable def g0 (_r t : ℝ) : ℝ := t
noncomputable def g1 (r t : ℝ) : ℝ := (-1/4 + r/4) + (3 - 2*r)*t
noncomputable def g2 (_r t : ℝ) : ℝ := t

/-- All three bands are positive on the two brackets: hence `G ≥ 0`. -/
lemma g_pos {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) :
    0 < g0 r t ∧ 0 < g1 r t ∧ 0 < g2 r t := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  refine ⟨by unfold g0; linarith, ?_, by unfold g2; linarith⟩
  unfold g1
  nlinarith [hr1, hr2, ht1, ht2]

/-- The abscissas at `x = 2/5` are positive and `< 1`. -/
lemma cL_mem {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) :
    ∀ i ∈ range 5, 0 < cL r t i ∧ cL r t i < 1 := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  intro i hi
  have hi' := mem_range.1 hi
  interval_cases i <;> simp only [cL] <;>
    constructor <;> nlinarith [hr1, hr2, ht1, ht2]




set_option maxHeartbeats 2000000 in
/-- `b > 0` at `x = 2/5`, on the two brackets. -/
lemma bL_pos {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) :
    ∀ i ∈ range 5, 0 < bL r t i := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  intro i hi
  have hi' := mem_range.1 hi
  interval_cases i <;> simp only [bL] <;> nlinarith [hr1, hr2, ht1, ht2]

set_option maxHeartbeats 2000000 in
/-- `b > 0` at `x = 21/50`. -/
lemma bR_pos {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) :
    ∀ i ∈ range 5, 0 < bR r t i := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  intro i hi
  have hi' := mem_range.1 hi
  interval_cases i <;> simp only [bR] <;> nlinarith [hr1, hr2, ht1, ht2]




/-- The relabelling that sorts the five-stage abscissas: `perm5 k` is the original stage
index becoming stage `k`.  It is the same at both endpoints. -/
def perm5 : ℕ → ℕ := fun k =>
  match k with
  | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | _ => 5

lemma perm5_mem : ∀ k ∈ range 5, perm5 k ∈ range 5 := by
  intro k hk
  have := mem_range.1 hk
  interval_cases k <;> simp [perm5]

/-- The abscissas at `x = 2/5` are strictly ordered by `perm5`. -/
lemma cL_sorted {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) :
    ∀ i ∈ range 5, ∀ j ∈ range 5, i < j → cL r t (perm5 i) < cL r t (perm5 j) := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  intro i hi j hj hij
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  interval_cases i <;> interval_cases j <;> simp only [perm5, cL] <;>
    first
      | exact absurd hij (by omega)
      | nlinarith [hr1, hr2, ht1, ht2]

/-- The same at `x = 21/50`. -/
lemma cR_sorted {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) :
    ∀ i ∈ range 5, ∀ j ∈ range 5, i < j → cR r t (perm5 i) < cR r t (perm5 j) := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  intro i hi j hj hij
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  interval_cases i <;> interval_cases j <;> simp only [perm5, cR] <;>
    first
      | exact absurd hij (by omega)
      | nlinarith [hr1, hr2, ht1, ht2]


/-- The coefficient matrix at `x = 2/5`: `A i j = G i j · v j / v i`, with `G`
circulant of bandwidth `3`, so fifteen entries are nonzero. -/
noncomputable def AL (r t : ℝ) : ℕ → ℕ → ℝ := fun i j =>
  match i, j with
  | 0, 0 => ((1 : ℝ)*t)
  | 0, 1 => (((-5/8 : ℝ) + (5/8 : ℝ)*r) + ((15/2 : ℝ) + (-5 : ℝ)*r)*t)
  | 0, 2 => ((6 : ℝ)*t)
  | 1, 1 => ((1 : ℝ)*t)
  | 1, 2 => (((-3/5 : ℝ) + (3/5 : ℝ)*r) + ((36/5 : ℝ) + (-24/5 : ℝ)*r)*t)
  | 1, 3 => ((21/20 : ℝ)*t)
  | 2, 2 => ((1 : ℝ)*t)
  | 2, 3 => (((-7/64 : ℝ) + (7/64 : ℝ)*r) + ((21/16 : ℝ) + (-7/8 : ℝ)*r)*t)
  | 2, 4 => ((11/48 : ℝ)*t)
  | 3, 0 => ((8/21 : ℝ)*t)
  | 3, 3 => ((1 : ℝ)*t)
  | 3, 4 => (((-11/84 : ℝ) + (11/84 : ℝ)*r) + ((11/7 : ℝ) + (-22/21 : ℝ)*r)*t)
  | 4, 0 => (((-2/11 : ℝ) + (2/11 : ℝ)*r) + ((24/11 : ℝ) + (-16/11 : ℝ)*r)*t)
  | 4, 1 => ((20/11 : ℝ)*t)
  | 4, 4 => ((1 : ℝ)*t)
  | _, _ => 0

/-- `bᵀAc = 1/6` at `x = 2/5`. -/
lemma m2_L (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∑ i ∈ range 5, bL r t i * (∑ j ∈ range 5, AL r t i j * cL r t j) = 1/6 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bL, cL, AL]
  linear_combination ((72829/5280 : ℝ) + (-106393/176 : ℝ)*t + (287125/44 : ℝ)*t^2 + (-128690/11 : ℝ)*t^3 + (190320/11 : ℝ)*t^4 + (-103/352 : ℝ)*r + (1981/176 : ℝ)*r*t + (-7237/44 : ℝ)*r*t^2 + (11768/11 : ℝ)*r*t^3 + (-28560/11 : ℝ)*r*t^4) * hr + ((-91825/11 : ℝ) + (1292700/11 : ℝ)*t + (41065/11 : ℝ)*r + (-578100/11 : ℝ)*r*t) * ht3


/-- The coefficient matrix at `x = 21/50`: `A i j = G i j · v j / v i`, with `G`
circulant of bandwidth `3`, so fifteen entries are nonzero. -/
noncomputable def AR (r t : ℝ) : ℕ → ℕ → ℝ := fun i j =>
  match i, j with
  | 0, 0 => ((1 : ℝ)*t)
  | 0, 1 => (((-25/42 : ℝ) + (25/42 : ℝ)*r) + ((50/7 : ℝ) + (-100/21 : ℝ)*r)*t)
  | 0, 2 => ((40/7 : ℝ)*t)
  | 1, 1 => ((1 : ℝ)*t)
  | 1, 2 => (((-3/5 : ℝ) + (3/5 : ℝ)*r) + ((36/5 : ℝ) + (-24/5 : ℝ)*r)*t)
  | 1, 3 => ((21/20 : ℝ)*t)
  | 2, 2 => ((1 : ℝ)*t)
  | 2, 3 => (((-7/64 : ℝ) + (7/64 : ℝ)*r) + ((21/16 : ℝ) + (-7/8 : ℝ)*r)*t)
  | 2, 4 => ((11/48 : ℝ)*t)
  | 3, 0 => ((2/5 : ℝ)*t)
  | 3, 3 => ((1 : ℝ)*t)
  | 3, 4 => (((-11/84 : ℝ) + (11/84 : ℝ)*r) + ((11/7 : ℝ) + (-22/21 : ℝ)*r)*t)
  | 4, 0 => (((-21/110 : ℝ) + (21/110 : ℝ)*r) + ((126/55 : ℝ) + (-84/55 : ℝ)*r)*t)
  | 4, 1 => ((20/11 : ℝ)*t)
  | 4, 4 => ((1 : ℝ)*t)
  | _, _ => 0

/-- `bᵀAc = 1/6` at `x = 21/50`. -/
lemma m2_R (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∑ i ∈ range 5, bR r t i * (∑ j ∈ range 5, AR r t i j * cR r t j) = 1/6 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bR, cR, AR]
  linear_combination ((72829/5280 : ℝ) + (-106393/176 : ℝ)*t + (287125/44 : ℝ)*t^2 + (-128690/11 : ℝ)*t^3 + (190320/11 : ℝ)*t^4 + (-103/352 : ℝ)*r + (1981/176 : ℝ)*r*t + (-7237/44 : ℝ)*r*t^2 + (11768/11 : ℝ)*r*t^3 + (-28560/11 : ℝ)*r*t^4) * hr + ((-91825/11 : ℝ) + (1292700/11 : ℝ)*t + (41065/11 : ℝ)*r + (-578100/11 : ℝ)*r*t) * ht3

/-- The certificate `R = D X D` at `x = 2/5`, symmetric of rank 3. -/
noncomputable def RL (r t : ℝ) : ℕ → ℕ → ℝ := fun i j =>
  match i, j with
  | 0, 0 => (((2432582342042/436868392059 : ℝ) + (-1072554075146/436868392059 : ℝ)*r) + ((-566945602153000/4805552312649 : ℝ) + (253267596038720/4805552312649 : ℝ)*r)*t + ((375911496195520/533950256961 : ℝ) + (-56026053765760/177983418987 : ℝ)*r)*t^2)
  | 0, 1 => (((3027916069865/436868392059 : ℝ) + (-1332773211425/436868392059 : ℝ)*r) + ((-610279779694900/4805552312649 : ℝ) + (272443836511760/4805552312649 : ℝ)*r)*t + ((351811374126400/533950256961 : ℝ) + (-52424073023200/177983418987 : ℝ)*r)*t^2)
  | 0, 2 => (((-4175843757740/145622797353 : ℝ) + (1863860112140/145622797353 : ℝ)*r) + ((910829921396080/1601850770883 : ℝ) + (-407302150207424/1601850770883 : ℝ)*r)*t + ((-562002984438400/177983418987 : ℝ) + (83781476588800/59327806329 : ℝ)*r)*t^2)
  | 0, 3 => (((15559727890819/582491189412 : ℝ) + (-6963524953819/582491189412 : ℝ)*r) + ((-873909478869035/1601850770883 : ℝ) + (390877136538448/1601850770883 : ℝ)*r)*t + ((556938577595960/177983418987 : ℝ) + (-83023100701520/59327806329 : ℝ)*r)*t^2)
  | 0, 4 => (((-1412912949131/158861233476 : ℝ) + (636457808915/158861233476 : ℝ)*r) + ((81840408643195/436868392059 : ℝ) + (-36615361190528/436868392059 : ℝ)*r)*t + ((-53291400390040/48540932451 : ℝ) + (7945043805040/16180310817 : ℝ)*r)*t^2)
  | 1, 0 => (((3027916069865/436868392059 : ℝ) + (-1332773211425/436868392059 : ℝ)*r) + ((-610279779694900/4805552312649 : ℝ) + (272443836511760/4805552312649 : ℝ)*r)*t + ((351811374126400/533950256961 : ℝ) + (-52424073023200/177983418987 : ℝ)*r)*t^2)
  | 1, 1 => (((16836154071925/873736784118 : ℝ) + (-7432796589325/873736784118 : ℝ)*r) + ((-1998550852104250/4805552312649 : ℝ) + (892796060366000/4805552312649 : ℝ)*r)*t + ((1396568628610000/533950256961 : ℝ) + (-208127228968000/177983418987 : ℝ)*r)*t^2)
  | 1, 2 => (((-7707784297790/145622797353 : ℝ) + (3451914349550/145622797353 : ℝ)*r) + ((1752184185599800/1601850770883 : ℝ) + (-783417281433920/1601850770883 : ℝ)*r)*t + ((-1178717653340800/177983418987 : ℝ) + (175721345838400/59327806329 : ℝ)*r)*t^2)
  | 1, 3 => (((52140520738775/1164982378824 : ℝ) + (-23359535127215/1164982378824 : ℝ)*r) + ((-2878034643806875/3203701541766 : ℝ) + (643813205788270/1601850770883 : ℝ)*r)*t + ((928510597758800/177983418987 : ℝ) + (-138424419982100/59327806329 : ℝ)*r)*t^2)
  | 1, 4 => (((-3639084255055/317722466952 : ℝ) + (1633192855735/317722466952 : ℝ)*r) + ((189743976071675/873736784118 : ℝ) + (-42434456745110/436868392059 : ℝ)*r)*t + ((-57695715762400/48540932451 : ℝ) + (8600591997700/16180310817 : ℝ)*r)*t^2)
  | 2, 0 => (((-4175843757740/145622797353 : ℝ) + (1863860112140/145622797353 : ℝ)*r) + ((910829921396080/1601850770883 : ℝ) + (-407302150207424/1601850770883 : ℝ)*r)*t + ((-562002984438400/177983418987 : ℝ) + (83781476588800/59327806329 : ℝ)*r)*t^2)
  | 2, 1 => (((-7707784297790/145622797353 : ℝ) + (3451914349550/145622797353 : ℝ)*r) + ((1752184185599800/1601850770883 : ℝ) + (-783417281433920/1601850770883 : ℝ)*r)*t + ((-1178717653340800/177983418987 : ℝ) + (175721345838400/59327806329 : ℝ)*r)*t^2)
  | 2, 2 => (((8496917020136/48540932451 : ℝ) + (-3791551930280/48540932451 : ℝ)*r) + ((-1884168681070240/533950256961 : ℝ) + (842749190256896/533950256961 : ℝ)*r)*t + ((1227738526385920/59327806329 : ℝ) + (-183026629818880/19775935443 : ℝ)*r)*t^2)
  | 2, 3 => (((-15227470834709/97081864902 : ℝ) + (6809906904941/97081864902 : ℝ)*r) + ((1685429097855650/533950256961 : ℝ) + (-753734103275944/533950256961 : ℝ)*r)*t + ((-1078733881321040/59327806329 : ℝ) + (160801611881120/19775935443 : ℝ)*r)*t^2)
  | 2, 4 => (((1227457355389/26476872246 : ℝ) + (-550148449573/26476872246 : ℝ)*r) + ((-133993038880210/145622797353 : ℝ) + (59923137486200/145622797353 : ℝ)*r)*t + ((83726042317840/16180310817 : ℝ) + (-12481604120800/5393436939 : ℝ)*r)*t^2)
  | 3, 0 => (((15559727890819/582491189412 : ℝ) + (-6963524953819/582491189412 : ℝ)*r) + ((-873909478869035/1601850770883 : ℝ) + (390877136538448/1601850770883 : ℝ)*r)*t + ((556938577595960/177983418987 : ℝ) + (-83023100701520/59327806329 : ℝ)*r)*t^2)
  | 3, 1 => (((52140520738775/1164982378824 : ℝ) + (-23359535127215/1164982378824 : ℝ)*r) + ((-2878034643806875/3203701541766 : ℝ) + (643813205788270/1601850770883 : ℝ)*r)*t + ((928510597758800/177983418987 : ℝ) + (-138424419982100/59327806329 : ℝ)*r)*t^2)
  | 3, 2 => (((-15227470834709/97081864902 : ℝ) + (6809906904941/97081864902 : ℝ)*r) + ((1685429097855650/533950256961 : ℝ) + (-753734103275944/533950256961 : ℝ)*r)*t + ((-1078733881321040/59327806329 : ℝ) + (160801611881120/19775935443 : ℝ)*r)*t^2)
  | 3, 3 => (((220055326578829/1553309838432 : ℝ) + (-98352838359013/1553309838432 : ℝ)*r) + ((-12255107024353445/4271602055688 : ℝ) + (684986494855607/533950256961 : ℝ)*r)*t + ((979853255687635/59327806329 : ℝ) + (-146066384066890/19775935443 : ℝ)*r)*t^2)
  | 3, 4 => (((-18390703784117/423629955936 : ℝ) + (8229909812285/423629955936 : ℝ)*r) + ((1026942909431845/1164982378824 : ℝ) + (-57417799947529/145622797353 : ℝ)*r)*t + ((-81749970841175/16180310817 : ℝ) + (12187066166870/5393436939 : ℝ)*r)*t^2)
  | 4, 0 => (((-1412912949131/158861233476 : ℝ) + (636457808915/158861233476 : ℝ)*r) + ((81840408643195/436868392059 : ℝ) + (-36615361190528/436868392059 : ℝ)*r)*t + ((-53291400390040/48540932451 : ℝ) + (7945043805040/16180310817 : ℝ)*r)*t^2)
  | 4, 1 => (((-3639084255055/317722466952 : ℝ) + (1633192855735/317722466952 : ℝ)*r) + ((189743976071675/873736784118 : ℝ) + (-42434456745110/436868392059 : ℝ)*r)*t + ((-57695715762400/48540932451 : ℝ) + (8600591997700/16180310817 : ℝ)*r)*t^2)
  | 4, 2 => (((1227457355389/26476872246 : ℝ) + (-550148449573/26476872246 : ℝ)*r) + ((-133993038880210/145622797353 : ℝ) + (59923137486200/145622797353 : ℝ)*r)*t + ((83726042317840/16180310817 : ℝ) + (-12481604120800/5393436939 : ℝ)*r)*t^2)
  | 4, 3 => (((-18390703784117/423629955936 : ℝ) + (8229909812285/423629955936 : ℝ)*r) + ((1026942909431845/1164982378824 : ℝ) + (-57417799947529/145622797353 : ℝ)*r)*t + ((-81749970841175/16180310817 : ℝ) + (12187066166870/5393436939 : ℝ)*r)*t^2)
  | 4, 4 => (((1659457400749/115535442528 : ℝ) + (-737786879749/115535442528 : ℝ)*r) + ((-94154658956885/317722466952 : ℝ) + (5260823276411/39715308369 : ℝ)*r)*t + ((7567814582635/4412812041 : ℝ) + (-1127989696450/1470937347 : ℝ)*r)*t^2)
  | _, _ => 0

/-- `R` is symmetric at `x = 2/5`. -/
lemma RL_symm (r t : ℝ) : ∀ i ∈ range 5, ∀ j ∈ range 5, RL r t i j = RL r t j i := by
  intro i hi j hj
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  interval_cases i <;> interval_cases j <;> simp [RL]

/-- Entry `(0,0)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_0_0 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 0 k * AL r t k 0)
      + (∑ k ∈ range 5, RL r t 0 k * AL r t k 0) - bL r t 0 * bL r t 0 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((255924680059408/24027761563245 : ℝ) + (-693602857719688/4805552312649 : ℝ)*t + (-22368240233270720/4805552312649 : ℝ)*t^2 + (3630339288901120/533950256961 : ℝ)*t^3 + (-5944434672025600/533950256961 : ℝ)*t^4) * hr + ((-169516886608000/26259848703 : ℝ) + (-19869502005939200/177983418987 : ℝ)*t + (75812058536960/26259848703 : ℝ)*r + (26657633208524800/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(0,1)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_0_1 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 0 k * AL r t k 1)
      + (∑ k ∈ range 5, RL r t 1 k * AL r t k 0) - bL r t 0 * bL r t 1 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((-208969961557462/4805552312649 : ℝ) + (8705209386858560/4805552312649 : ℝ)*t + (-82643980366188200/4805552312649 : ℝ)*t^2 + (13859677821822400/533950256961 : ℝ)*t^3 + (-17110160027392000/533950256961 : ℝ)*t^4) * hr + ((723558618632000/26259848703 : ℝ) + (-57151989526400000/177983418987 : ℝ)*t + (-323585400395200/26259848703 : ℝ)*r + (76677294507328000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(0,2)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_0_2 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 0 k * AL r t k 2)
      + (∑ k ∈ range 5, RL r t 2 k * AL r t k 0) - bL r t 0 * bL r t 2 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((169214717536208/8009253854415 : ℝ) + (-3520332219443552/1601850770883 : ℝ)*t + (75902906837652320/1601850770883 : ℝ)*t^2 + (-12678091128075520/177983418987 : ℝ)*t^3 + (17577405501030400/177983418987 : ℝ)*t^4) * hr + ((-127144327260800/8753282901 : ℝ) + (58688927435110400/59327806329 : ℝ)*t + (56859578815360/8753282901 : ℝ)*r + (-78739396829286400/177983418987 : ℝ)*r*t) * ht3

/-- Entry `(0,3)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_0_3 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 0 k * AL r t k 3)
      + (∑ k ∈ range 5, RL r t 3 k * AL r t k 0) - bL r t 0 * bL r t 3 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((-48722270600017/8009253854415 : ℝ) + (2231961925833262/1601850770883 : ℝ)*t + (-58002975784523140/1601850770883 : ℝ)*t^2 + (9609110227021760/177983418987 : ℝ)*t^3 + (-13669420439091200/177983418987 : ℝ)*t^4) * hr + ((42564534044200/8753282901 : ℝ) + (-45617295870294400/59327806329 : ℝ)*t + (-19034550694040/8753282901 : ℝ)*r + (61202062592921600/177983418987 : ℝ)*r*t) * ht3

/-- Entry `(0,4)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_0_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 0 k * AL r t k 4)
      + (∑ k ∈ range 5, RL r t 4 k * AL r t k 0) - bL r t 0 * bL r t 4 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((-16584292112983/873736784118 : ℝ) + (102415282516309/436868392059 : ℝ)*t + (3920101362786320/436868392059 : ℝ)*t^2 + (-645666130779520/48540932451 : ℝ)*t^3 + (1030058137600000/48540932451 : ℝ)*t^4) * hr + ((27509152009600/2387258973 : ℝ) + (3436963348899200/16180310817 : ℝ)*t + (-12302158534400/2387258973 : ℝ)*r + (-4611175000614400/48540932451 : ℝ)*r*t) * ht3

/-- Entry `(1,1)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_1_1 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 1 k * AL r t k 1)
      + (∑ k ∈ range 5, RL r t 1 k * AL r t k 1) - bL r t 1 * bL r t 1 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((-943819251312910/4805552312649 : ℝ) + (35312989394596250/4805552312649 : ℝ)*t + (-253996283883349400/4805552312649 : ℝ)*t^2 + (42501294032776000/533950256961 : ℝ)*t^3 + (-49249019009440000/533950256961 : ℝ)*t^4) * hr + ((3257940494300000/26259848703 : ℝ) + (-164390202034400000/177983418987 : ℝ)*t + (-1457006539096000/26259848703 : ℝ)*r + (220552390038400000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(1,2)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_1_2 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 1 k * AL r t k 2)
      + (∑ k ∈ range 5, RL r t 2 k * AL r t k 1) - bL r t 1 * bL r t 2 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((690883564047628/1601850770883 : ℝ) + (-27918689430976040/1601850770883 : ℝ)*t + (247602911698974560/1601850770883 : ℝ)*t^2 + (-41526587905100800/177983418987 : ℝ)*t^3 + (50593914742528000/177983418987 : ℝ)*t^4) * hr + ((-2389602555464000/8753282901 : ℝ) + (168811049239040000/59327806329 : ℝ)*t + (1068657405716800/8753282901 : ℝ)*r + (-226483699624576000/177983418987 : ℝ)*r*t) * ht3

/-- Entry `(1,3)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_1_3 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 1 k * AL r t k 3)
      + (∑ k ∈ range 5, RL r t 3 k * AL r t k 1) - bL r t 1 * bL r t 3 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((-2298033853857623/6407403083532 : ℝ) + (45638789283940685/3203701541766 : ℝ)*t + (-194299865842382545/1601850770883 : ℝ)*t^2 + (32569776573912200/177983418987 : ℝ)*t^3 + (-39345368247584000/177983418987 : ℝ)*t^4) * hr + ((1983973405004500/8753282901 : ℝ) + (-131212251041200000/59327806329 : ℝ)*t + (-887257419013700/8753282901 : ℝ)*r + (176039762275496000/177983418987 : ℝ)*r*t) * ht3

/-- Entry `(1,4)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_1_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 1 k * AL r t k 4)
      + (∑ k ∈ range 5, RL r t 4 k * AL r t k 1) - bL r t 1 * bL r t 4 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((60352566196055/873736784118 : ℝ) + (-1326795102654245/436868392059 : ℝ)*t + (14017717973887895/436868392059 : ℝ)*t^2 + (-2356085581143400/48540932451 : ℝ)*t^3 + (2964867232000000/48540932451 : ℝ)*t^4) * hr + ((-104570878646000/2387258973 : ℝ) + (9885981542480000/16180310817 : ℝ)*t + (46766065117000/2387258973 : ℝ)*r + (-13263442954408000/48540932451 : ℝ)*r*t) * ht3

/-- Entry `(2,2)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_2_2 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 2 k * AL r t k 2)
      + (∑ k ∈ range 5, RL r t 2 k * AL r t k 2) - bL r t 2 * bL r t 2 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((-1831795714836992/2669751284805 : ℝ) + (18392575067764256/533950256961 : ℝ)*t + (-237711631035288704/533950256961 : ℝ)*t^2 + (39910320578544640/59327806329 : ℝ)*t^3 + (-51975536984473600/59327806329 : ℝ)*t^4) * hr + ((1280739038259200/2917760967 : ℝ) + (-173350811964108800/19775935443 : ℝ)*t + (-572765548925440/2917760967 : ℝ)*r + (232574481759846400/59327806329 : ℝ)*r*t) * ht3

/-- Entry `(2,3)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_2_3 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 2 k * AL r t k 3)
      + (∑ k ∈ range 5, RL r t 3 k * AL r t k 2) - bL r t 2 * bL r t 3 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((1393385029193248/2669751284805 : ℝ) + (-14105644527211090/533950256961 : ℝ)*t + (184342177304231548/533950256961 : ℝ)*t^2 + (-30887771956922720/59327806329 : ℝ)*t^3 + (40419814377420800/59327806329 : ℝ)*t^4) * hr + ((-974446723667200/2917760967 : ℝ) + (134740913303852800/19775935443 : ℝ)*t + (435786733460960/2917760967 : ℝ)*r + (-180773928108300800/59327806329 : ℝ)*r*t) * ht3

/-- Entry `(2,4)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_2_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 2 k * AL r t k 4)
      + (∑ k ∈ range 5, RL r t 4 k * AL r t k 2) - bL r t 2 * bL r t 4 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((-4178110706665/145622797353 : ℝ) + (559305995809040/145622797353 : ℝ)*t + (-13076112897980228/145622797353 : ℝ)*t^2 + (2193973193029600/16180310817 : ℝ)*t^3 + (-3045832038400000/16180310817 : ℝ)*t^4) * hr + ((16026175989200/795752991 : ℝ) + (-10151843699398400/5393436939 : ℝ)*t + (-7167014842000/795752991 : ℝ)*r + (13620130499929600/16180310817 : ℝ)*r*t) * ht3

/-- Entry `(3,3)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_3_3 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 3 k * AL r t k 3)
      + (∑ k ∈ range 5, RL r t 3 k * AL r t k 3) - bL r t 3 * bL r t 3 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((-4171593321869183/10679005139220 : ℝ) + (85704022529585593/4271602055688 : ℝ)*t + (-142698436438934516/533950256961 : ℝ)*t^2 + (23820667425552760/59327806329 : ℝ)*t^3 + (-31433275904262400/59327806329 : ℝ)*t^4) * hr + ((729880381970600/2917760967 : ℝ) + (-104730507122250800/19775935443 : ℝ)*t + (-326412402263290/2917760967 : ℝ)*r + (140510705749187200/59327806329 : ℝ)*r*t) * ht3

/-- Entry `(3,4)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_3_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 3 k * AL r t k 4)
      + (∑ k ∈ range 5, RL r t 4 k * AL r t k 3) - bL r t 3 * bL r t 4 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((6858195120329/2329964757648 : ℝ) + (-349288694813296/145622797353 : ℝ)*t + (20006495105971577/291245594706 : ℝ)*t^2 + (-1668979650569840/16180310817 : ℝ)*t^3 + (2368652115200000/16180310817 : ℝ)*t^4) * hr + ((-47263798225/13045131 : ℝ) + (7890757124244400/5393436939 : ℝ)*t + (21137625425/13045131 : ℝ)*r + (-10586559799188800/16180310817 : ℝ)*r*t) * ht3

/-- Entry `(4,4)` of `M = R A + Aᵗ R − b bᵗ` vanishes at `x = 2/5`. -/
lemma Mzero_L_4_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RL r t 4 k * AL r t k 4)
      + (∑ k ∈ range 5, RL r t 4 k * AL r t k 4) - bL r t 4 * bL r t 4 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RL, AL, bL]
  linear_combination ((10489709770687/317722466952 : ℝ) + (-111427432908197/317722466952 : ℝ)*t + (-687283305517421/39715308369 : ℝ)*t^2 + (114390124331080/4412812041 : ℝ)*t^3 + (-178489600000000/4412812041 : ℝ)*t^4) * hr + ((-4354952715550/217023543 : ℝ) + (-594516833265200/1470937347 : ℝ)*t + (1947619002800/217023543 : ℝ)*r + (797627804800000/4412812041 : ℝ)*r*t) * ht3

/-- `R e = b` at `x = 2/5`. -/
lemma RL_rowsum (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∀ i ∈ range 5, ∑ j ∈ range 5, RL r t i j = bL r t i := by
  intro i hi
  have hi' := mem_range.1 hi
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  interval_cases i <;> simp only [RL, bL]
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3

/-- **`M = 0` at `x = 2/5`**, assembled from the fifteen entry lemmas. -/
lemma ML_zero (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∀ i ∈ range 5, ∀ j ∈ range 5,
      (∑ k ∈ range 5, RL r t i k * AL r t k j)
        + (∑ k ∈ range 5, RL r t j k * AL r t k i) - bL r t i * bL r t j = 0 := by
  intro i hi j hj
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  interval_cases i <;> interval_cases j
  case _ => exact Mzero_L_0_0 r t hr ht3
  case _ => exact Mzero_L_0_1 r t hr ht3
  case _ => exact Mzero_L_0_2 r t hr ht3
  case _ => exact Mzero_L_0_3 r t hr ht3
  case _ => exact Mzero_L_0_4 r t hr ht3
  case _ => linear_combination Mzero_L_0_1 r t hr ht3
  case _ => exact Mzero_L_1_1 r t hr ht3
  case _ => exact Mzero_L_1_2 r t hr ht3
  case _ => exact Mzero_L_1_3 r t hr ht3
  case _ => exact Mzero_L_1_4 r t hr ht3
  case _ => linear_combination Mzero_L_0_2 r t hr ht3
  case _ => linear_combination Mzero_L_1_2 r t hr ht3
  case _ => exact Mzero_L_2_2 r t hr ht3
  case _ => exact Mzero_L_2_3 r t hr ht3
  case _ => exact Mzero_L_2_4 r t hr ht3
  case _ => linear_combination Mzero_L_0_3 r t hr ht3
  case _ => linear_combination Mzero_L_1_3 r t hr ht3
  case _ => linear_combination Mzero_L_2_3 r t hr ht3
  case _ => exact Mzero_L_3_3 r t hr ht3
  case _ => exact Mzero_L_3_4 r t hr ht3
  case _ => linear_combination Mzero_L_0_4 r t hr ht3
  case _ => linear_combination Mzero_L_1_4 r t hr ht3
  case _ => linear_combination Mzero_L_2_4 r t hr ht3
  case _ => linear_combination Mzero_L_3_4 r t hr ht3
  case _ => exact Mzero_L_4_4 r t hr ht3


/-! ## Positive semidefiniteness of the certificate

Since `z = Bᵗv` is constant along the null-direction segment, the reduced matrix `S` is the
*same* at both endpoints, so one proof covers both.  `R = D X D` with `X = B S Bᵗ`, and
`xᵗRx = (Dx)ᵗX(Dx)`, `xᵗXx = (Bᵗx)ᵗS(Bᵗx)`; so it suffices that `S` be positive
semidefinite. -/

/-- The `3 × 3` reduced matrix `S`, with `X = B S Bᵗ`.  It is the *same* at both
endpoints of the null-direction segment, because `z = Bᵗv` is constant there. -/
noncomputable def Sm5 (r t : ℝ) : ℕ → ℕ → ℝ := fun i j =>
  match i, j with
  | 0, 0 => (((540575/176418 : ℝ) + (-235175/176418 : ℝ)*r) + ((-5430250/88209 : ℝ) + (2423600/88209 : ℝ)*r)*t + ((3490000/9801 : ℝ) + (-520000/3267 : ℝ)*r)*t^2)
  | 0, 1 => (((13201600/2192157 : ℝ) + (-5798800/2192157 : ℝ)*r) + ((-88004000/730719 : ℝ) + (117897200/2192157 : ℝ)*r)*t + ((45674000/66429 : ℝ) + (-6806000/22143 : ℝ)*r)*t^2)
  | 0, 2 => (((19765600/2192157 : ℝ) + (-8846000/2192157 : ℝ)*r) + ((-134042500/730719 : ℝ) + (179890300/2192157 : ℝ)*r)*t + ((23519000/22143 : ℝ) + (-31555000/66429 : ℝ)*r)*t^2)
  | 1, 0 => (((13201600/2192157 : ℝ) + (-5798800/2192157 : ℝ)*r) + ((-88004000/730719 : ℝ) + (117897200/2192157 : ℝ)*r)*t + ((45674000/66429 : ℝ) + (-6806000/22143 : ℝ)*r)*t^2)
  | 1, 1 => (((11801351800/599270771 : ℝ) + (-5226121000/599270771 : ℝ)*r) + ((-2867027492000/6591978481 : ℝ) + (1281191270400/6591978481 : ℝ)*r)*t + ((17593428000000/6591978481 : ℝ) + (-7867468704000/6591978481 : ℝ)*r)*t^2)
  | 1, 2 => (((11902021800/599270771 : ℝ) + (-5323642000/599270771 : ℝ)*r) + ((-2643804289000/6591978481 : ℝ) + (1181880720200/6591978481 : ℝ)*r)*t + ((14875536816000/6591978481 : ℝ) + (-6652251120000/6591978481 : ℝ)*r)*t^2)
  | 2, 0 => (((19765600/2192157 : ℝ) + (-8846000/2192157 : ℝ)*r) + ((-134042500/730719 : ℝ) + (179890300/2192157 : ℝ)*r)*t + ((23519000/22143 : ℝ) + (-31555000/66429 : ℝ)*r)*t^2)
  | 2, 1 => (((11902021800/599270771 : ℝ) + (-5323642000/599270771 : ℝ)*r) + ((-2643804289000/6591978481 : ℝ) + (1181880720200/6591978481 : ℝ)*r)*t + ((14875536816000/6591978481 : ℝ) + (-6652251120000/6591978481 : ℝ)*r)*t^2)
  | 2, 2 => (((16240300350/599270771 : ℝ) + (-7237550950/599270771 : ℝ)*r) + ((-3601221989500/6591978481 : ℝ) + (1609912085300/6591978481 : ℝ)*r)*t + ((20776305840000/6591978481 : ℝ) + (-9290248032000/6591978481 : ℝ)*r)*t^2)
  | _, _ => 0

/-- Leading principal minor of `S`. -/
noncomputable def sm5_1 (r t : ℝ) : ℝ := (((540575/176418 : ℝ) + (-235175/176418 : ℝ)*r) + ((-5430250/88209 : ℝ) + (2423600/88209 : ℝ)*r)*t + ((3490000/9801 : ℝ) + (-520000/3267 : ℝ)*r)*t^2)

/-- Leading principal minor of `S`. -/
noncomputable def sm5_2 (r t : ℝ) : ℝ := (((45467650400000/4805552312649 : ℝ) + (-20324507270000/4805552312649 : ℝ)*r) + ((-924631673200000/4805552312649 : ℝ) + (413492875300000/4805552312649 : ℝ)*r)*t + ((1783734739000000/1601850770883 : ℝ) + (-2393111101600000/4805552312649 : ℝ)*r)*t^2)

/-- Leading principal minor of `S`. -/
noncomputable def sm5_3 (r t : ℝ) : ℝ := (((1927617502000000/1744415489491587 : ℝ) + (-31917142000000/64607981092281 : ℝ)*r) + ((-13059661360000000/581471829830529 : ℝ) + (5840292728000000/581471829830529 : ℝ)*r)*t + ((6867129880000000/52861075439139 : ℝ) + (-3071051240000000/52861075439139 : ℝ)*r)*t^2)

lemma sm5_1_pos {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) : 0 < sm5_1 r t := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  unfold sm5_1
  nlinarith [hr1, hr2, ht1, ht2, mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hr1),
    sq_nonneg t, sq_nonneg (t - 35127/1000000), sq_nonneg (r - 2236067/1000000)]

lemma sm5_2_pos {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) : 0 < sm5_2 r t := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  unfold sm5_2
  nlinarith [hr1, hr2, ht1, ht2, mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hr1),
    sq_nonneg t, sq_nonneg (t - 35127/1000000), sq_nonneg (r - 2236067/1000000)]

lemma sm5_3_pos {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) : 0 < sm5_3 r t := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  unfold sm5_3
  nlinarith [hr1, hr2, ht1, ht2, mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hr1),
    sq_nonneg t, sq_nonneg (t - 35127/1000000), sq_nonneg (r - 2236067/1000000)]



/-! ### Positive semidefiniteness, via an abstract completion of squares

Unfolding `Sm5` inside a `ring` call blows up on the size of the literals, so the
completion-of-squares identity is proved once for *arbitrary* entries and instantiated.  The
minors `sm5_2`, `sm5_3` are stored pre-reduced (degree `≤ 2` in `t`), while the raw
expressions `S₀₀S₁₁ − S₀₁²` and `det S` have degree `4` and `6`; the two are matched by
`linear_combination` against `hr` and `ht3`. -/

/-- Completion of squares for a symmetric `3 × 3` form. -/
lemma sos3 (a b e d f g x0 x1 x2 : ℝ) :
    a * (a*d - b^2) *
      (a*x0^2 + 2*b*x0*x1 + 2*e*x0*x2 + d*x1^2 + 2*f*x1*x2 + g*x2^2)
    = (a*d - b^2) * (a*x0 + b*x1 + e*x2)^2
      + ((a*d - b^2)*x1 + (a*f - b*e)*x2)^2
      + a * (a*(d*g - f^2) - b*(b*g - f*e) + e*(b*f - d*e)) * x2^2 := by
  ring

/-- Sylvester, made explicit: positive leading minors give a nonnegative form. -/
lemma psd_of_minors {a b e d f g : ℝ}
    (h1 : 0 < a) (h2 : 0 < a*d - b^2)
    (h3 : 0 < a*(d*g - f^2) - b*(b*g - f*e) + e*(b*f - d*e)) (x0 x1 x2 : ℝ) :
    0 ≤ a*x0^2 + 2*b*x0*x1 + 2*e*x0*x2 + d*x1^2 + 2*f*x1*x2 + g*x2^2 := by
  have key := sos3 a b e d f g x0 x1 x2
  have hrhs : 0 ≤ (a*d - b^2) * (a*x0 + b*x1 + e*x2)^2
      + ((a*d - b^2)*x1 + (a*f - b*e)*x2)^2
      + a * (a*(d*g - f^2) - b*(b*g - f*e) + e*(b*f - d*e)) * x2^2 := by positivity
  nlinarith [key, hrhs, mul_pos h1 h2]

/-- The stored second minor equals the raw expression. -/
lemma sm5_2_eq (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    Sm5 r t 0 0 * Sm5 r t 1 1 - Sm5 r t 0 1 ^ 2 = sm5_2 r t := by
  simp only [Sm5, sm5_2]
  linear_combination ((1208736037194500/17620358479713 : ℝ) + (-689439715931200000/193823943276843 : ℝ)*t + (28161922762795280000/581471829830529 : ℝ)*t^2 + (-14222502233842400000/193823943276843 : ℝ)*t^3 + (228499834228000000/2392888188603 : ℝ)*t^4) * hr + ((-68740180400000000/1601850770883 : ℝ) + (509964811784000000/533950256961 : ℝ)*t + (30741531857600000/1601850770883 : ℝ)*r + (-76021068872000000/177983418987 : ℝ)*r*t) * ht3

/-- The stored third minor equals `det S`. -/
lemma sm5_3_eq (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    Sm5 r t 0 0 * (Sm5 r t 1 1 * Sm5 r t 2 2 - Sm5 r t 1 2 ^ 2)
      - Sm5 r t 0 1 * (Sm5 r t 0 1 * Sm5 r t 2 2 - Sm5 r t 1 2 * Sm5 r t 0 2)
      + Sm5 r t 0 2 * (Sm5 r t 0 1 * Sm5 r t 1 2 - Sm5 r t 1 1 * Sm5 r t 0 2)
      = sm5_3 r t := by
  simp only [Sm5, sm5_3]
  linear_combination ((-15601303062242825000/211074274228482027 : ℝ) + (116946357663619750000/23452697136498003 : ℝ)*t + (-8666180981443154500000/70358091409494009 : ℝ)*t^2 + (2960791080491210000000/2132063376045273 : ℝ)*t^3 + (-4810143336007280000000/710687792015091 : ℝ)*t^4 + (1106505793006800000000/96513156940321 : ℝ)*t^5 + (-12281454350432000000000/868618412462889 : ℝ)*t^6 + (116919142119875000/70358091409494009 : ℝ)*r + (-2300825989894250000/23452697136498003 : ℝ)*r*t + (171927905186925500000/70358091409494009 : ℝ)*r*t^2 + (-211246782763696000000/6396190128135819 : ℝ)*r*t^3 + (549439162377680000000/2132063376045273 : ℝ)*r*t^4 + (-8718115174050800000000/7817565712166001 : ℝ)*r*t^5 + (5567987606176000000000/2605855237388667 : ℝ)*r*t^6) * hr + ((25888678202000000000/581471829830529 : ℝ) + (-326610722291200000000/193823943276843 : ℝ)*t + (1419649065248000000000/64607981092281 : ℝ)*t^2 + (-2016032630528000000000/21535993697427 : ℝ)*t^3 + (-11577769664720000000/581471829830529 : ℝ)*r + (48688251622400000000/64607981092281 : ℝ)*r*t + (-70542929158400000000/7178664565809 : ℝ)*r*t^2 + (300532400384000000000/7178664565809 : ℝ)*r*t^3) * ht3

/-- **The quadratic form of `S` is nonnegative** on the two brackets. -/
lemma Sm5_psd {r t : ℝ} (hr2 : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300))
    (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) (x0 x1 x2 : ℝ) :
    0 ≤ Sm5 r t 0 0 * x0^2 + 2*Sm5 r t 0 1 * x0*x1 + 2*Sm5 r t 0 2 * x0*x2
      + Sm5 r t 1 1 * x1^2 + 2*Sm5 r t 1 2 * x1*x2 + Sm5 r t 2 2 * x2^2 := by
  refine psd_of_minors ?_ ?_ ?_ x0 x1 x2
  · have := sm5_1_pos hr ht; unfold sm5_1 at this; exact this
  · rw [sm5_2_eq r t hr2 ht3]; exact sm5_2_pos hr ht
  · rw [sm5_3_eq r t hr2 ht3]; exact sm5_3_pos hr ht

set_option maxRecDepth 20000 in
/-- Both ranges are concrete, so expand fully and close by `ring`. -/
lemma quadform_transfer (S B : ℕ → ℕ → ℝ) (x : ℕ → ℝ) :
    ∑ i ∈ range 5, ∑ j ∈ range 5,
        (∑ p ∈ range 3, ∑ q ∈ range 3, S p q * (B p i * B q j)) * (x i * x j)
      = ∑ p ∈ range 3, ∑ q ∈ range 3,
          S p q * ((∑ i ∈ range 5, B p i * x i) * (∑ j ∈ range 5, B q j * x j)) := by
  simp only [show (5:ℕ)=4+1 from rfl, show (3:ℕ)=2+1 from rfl,
    Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- The basis `B = [e | x | w]` of the invariant subspace, over `ℚ(√5)`. -/
noncomputable def Bm5 (r : ℝ) : ℕ → ℕ → ℝ := fun p i =>
  match p, i with
  | 0, 0 => 1 | 0, 1 => 1 | 0, 2 => 1 | 0, 3 => 1 | 0, 4 => 1
  | 1, 0 => 1 | 1, 1 => (r-1)/4 | 1, 2 => -(r+1)/4 | 1, 3 => -(r+1)/4 | 1, 4 => (r-1)/4
  | 2, 0 => 0 | 2, 1 => 1 | 2, 2 => (r-1)/2 | 2, 3 => -(r-1)/2 | 2, 4 => -1
  | _, _ => 0

/-- The quadratic form of `S` written as a double sum, for use with `quadform_transfer`. -/
lemma Sm5_psd_sum {r t : ℝ} (hr2 : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300))
    (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) (u : ℕ → ℝ) :
    0 ≤ ∑ p ∈ range 3, ∑ q ∈ range 3, Sm5 r t p q * (u p * u q) := by
  have h := Sm5_psd hr2 ht3 hr ht (u 0) (u 1) (u 2)
  have hsym1 : Sm5 r t 1 0 = Sm5 r t 0 1 := by simp [Sm5]
  have hsym2 : Sm5 r t 2 0 = Sm5 r t 0 2 := by simp [Sm5]
  have hsym3 : Sm5 r t 2 1 = Sm5 r t 1 2 := by simp [Sm5]
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hsym1, hsym2, hsym3]
  nlinarith [h]



/-- `X = B S Bᵗ`, the rank-3 matrix with `R = D X D`. -/
noncomputable def Xm5 (r t : ℝ) : ℕ → ℕ → ℝ := fun i j =>
  match i, j with
  | 0, 0 => (((30407279275525/873736784118 : ℝ) + (-13406925939325/873736784118 : ℝ)*r) + ((-3543410013456250/4805552312649 : ℝ) + (1582922475242000/4805552312649 : ℝ)*r)*t + ((2349446851222000/533950256961 : ℝ) + (-350162836036000/177983418987 : ℝ)*r)*t^2)
  | 0, 1 => (((15139580349325/873736784118 : ℝ) + (-6663866057125/873736784118 : ℝ)*r) + ((-1525699449237250/4805552312649 : ℝ) + (681109591279400/4805552312649 : ℝ)*r)*t + ((879528435316000/533950256961 : ℝ) + (-131060182558000/177983418987 : ℝ)*r)*t^2)
  | 0, 2 => (((-26099023485875/873736784118 : ℝ) + (11649125700875/873736784118 : ℝ)*r) + ((2846343504362750/4805552312649 : ℝ) + (-1272819219398200/4805552312649 : ℝ)*r)*t + ((-1756259326370000/533950256961 : ℝ) + (261817114340000/177983418987 : ℝ)*r)*t^2)
  | 0, 3 => (((55570456752925/873736784118 : ℝ) + (-24869731977925/873736784118 : ℝ)*r) + ((-6242210563350250/4805552312649 : ℝ) + (2791979546703200/4805552312649 : ℝ)*r)*t + ((3978132697114000/533950256961 : ℝ) + (-593022147868000/177983418987 : ℝ)*r)*t^2)
  | 0, 4 => (((-35322823728275/873736784118 : ℝ) + (15911445222875/873736784118 : ℝ)*r) + ((4092020432159750/4805552312649 : ℝ) + (-1830768059526400/4805552312649 : ℝ)*r)*t + ((-2664570019502000/533950256961 : ℝ) + (397252190252000/177983418987 : ℝ)*r)*t^2)
  | 1, 0 => (((15139580349325/873736784118 : ℝ) + (-6663866057125/873736784118 : ℝ)*r) + ((-1525699449237250/4805552312649 : ℝ) + (681109591279400/4805552312649 : ℝ)*r)*t + ((879528435316000/533950256961 : ℝ) + (-131060182558000/177983418987 : ℝ)*r)*t^2)
  | 1, 1 => (((16836154071925/873736784118 : ℝ) + (-7432796589325/873736784118 : ℝ)*r) + ((-1998550852104250/4805552312649 : ℝ) + (892796060366000/4805552312649 : ℝ)*r)*t + ((1396568628610000/533950256961 : ℝ) + (-208127228968000/177983418987 : ℝ)*r)*t^2)
  | 1, 2 => (((-19269460744475/873736784118 : ℝ) + (8629785873875/873736784118 : ℝ)*r) + ((2190230231999750/4805552312649 : ℝ) + (-979271601792400/4805552312649 : ℝ)*r)*t + ((-1473397066676000/533950256961 : ℝ) + (219651682298000/177983418987 : ℝ)*r)*t^2)
  | 1, 3 => (((37243229099125/873736784118 : ℝ) + (-16685382233725/873736784118 : ℝ)*r) + ((-4111478062581250/4805552312649 : ℝ) + (1839466302252200/4805552312649 : ℝ)*r)*t + ((2652887422168000/533950256961 : ℝ) + (-395498342806000/177983418987 : ℝ)*r)*t^2)
  | 1, 4 => (((-18195421275275/873736784118 : ℝ) + (8165964278675/873736784118 : ℝ)*r) + ((1897439760716750/4805552312649 : ℝ) + (-848689134902200/4805552312649 : ℝ)*r)*t + ((-1153914315248000/533950256961 : ℝ) + (172011839954000/177983418987 : ℝ)*r)*t^2)
  | 2, 0 => (((-26099023485875/873736784118 : ℝ) + (11649125700875/873736784118 : ℝ)*r) + ((2846343504362750/4805552312649 : ℝ) + (-1272819219398200/4805552312649 : ℝ)*r)*t + ((-1756259326370000/533950256961 : ℝ) + (261817114340000/177983418987 : ℝ)*r)*t^2)
  | 2, 1 => (((-19269460744475/873736784118 : ℝ) + (8629785873875/873736784118 : ℝ)*r) + ((2190230231999750/4805552312649 : ℝ) + (-979271601792400/4805552312649 : ℝ)*r)*t + ((-1473397066676000/533950256961 : ℝ) + (219651682298000/177983418987 : ℝ)*r)*t^2)
  | 2, 2 => (((26552865687925/873736784118 : ℝ) + (-11848599782125/873736784118 : ℝ)*r) + ((-2944013564172250/4805552312649 : ℝ) + (1316795609776400/4805552312649 : ℝ)*r)*t + ((1918341447478000/533950256961 : ℝ) + (-285979109092000/177983418987 : ℝ)*r)*t^2)
  | 2, 3 => (((-54383824409675/873736784118 : ℝ) + (24321096089075/873736784118 : ℝ)*r) + ((6019389635198750/4805552312649 : ℝ) + (-2691907511699800/4805552312649 : ℝ)*r)*t + ((-3852621004718000/533950256961 : ℝ) + (574291471004000/177983418987 : ℝ)*r)*t^2)
  | 2, 4 => (((30686433884725/873736784118 : ℝ) + (-13753711239325/873736784118 : ℝ)*r) + ((-3349825972005250/4805552312649 : ℝ) + (1498078437155000/4805552312649 : ℝ)*r)*t + ((2093151057946000/533950256961 : ℝ) + (-312040103020000/177983418987 : ℝ)*r)*t^2)
  | 3, 0 => (((55570456752925/873736784118 : ℝ) + (-24869731977925/873736784118 : ℝ)*r) + ((-6242210563350250/4805552312649 : ℝ) + (2791979546703200/4805552312649 : ℝ)*r)*t + ((3978132697114000/533950256961 : ℝ) + (-593022147868000/177983418987 : ℝ)*r)*t^2)
  | 3, 1 => (((37243229099125/873736784118 : ℝ) + (-16685382233725/873736784118 : ℝ)*r) + ((-4111478062581250/4805552312649 : ℝ) + (1839466302252200/4805552312649 : ℝ)*r)*t + ((2652887422168000/533950256961 : ℝ) + (-395498342806000/177983418987 : ℝ)*r)*t^2)
  | 3, 2 => (((-54383824409675/873736784118 : ℝ) + (24321096089075/873736784118 : ℝ)*r) + ((6019389635198750/4805552312649 : ℝ) + (-2691907511699800/4805552312649 : ℝ)*r)*t + ((-3852621004718000/533950256961 : ℝ) + (574291471004000/177983418987 : ℝ)*r)*t^2)
  | 3, 3 => (((112273125805525/873736784118 : ℝ) + (-50180019570925/873736784118 : ℝ)*r) + ((-12505211249340250/4805552312649 : ℝ) + (5591726488617200/4805552312649 : ℝ)*r)*t + ((7998802087246000/533950256961 : ℝ) + (-1192378645444000/177983418987 : ℝ)*r)*t^2)
  | 3, 4 => (((-65681084943275/873736784118 : ℝ) + (29392535043875/873736784118 : ℝ)*r) + ((7335306495941750/4805552312649 : ℝ) + (-3281017139858800/4805552312649 : ℝ)*r)*t + ((-4671426905210000/533950256961 : ℝ) + (696403780964000/177983418987 : ℝ)*r)*t^2)
  | 4, 0 => (((-35322823728275/873736784118 : ℝ) + (15911445222875/873736784118 : ℝ)*r) + ((4092020432159750/4805552312649 : ℝ) + (-1830768059526400/4805552312649 : ℝ)*r)*t + ((-2664570019502000/533950256961 : ℝ) + (397252190252000/177983418987 : ℝ)*r)*t^2)
  | 4, 1 => (((-18195421275275/873736784118 : ℝ) + (8165964278675/873736784118 : ℝ)*r) + ((1897439760716750/4805552312649 : ℝ) + (-848689134902200/4805552312649 : ℝ)*r)*t + ((-1153914315248000/533950256961 : ℝ) + (172011839954000/177983418987 : ℝ)*r)*t^2)
  | 4, 2 => (((30686433884725/873736784118 : ℝ) + (-13753711239325/873736784118 : ℝ)*r) + ((-3349825972005250/4805552312649 : ℝ) + (1498078437155000/4805552312649 : ℝ)*r)*t + ((2093151057946000/533950256961 : ℝ) + (-312040103020000/177983418987 : ℝ)*r)*t^2)
  | 4, 3 => (((-65681084943275/873736784118 : ℝ) + (29392535043875/873736784118 : ℝ)*r) + ((7335306495941750/4805552312649 : ℝ) + (-3281017139858800/4805552312649 : ℝ)*r)*t + ((-4671426905210000/533950256961 : ℝ) + (696403780964000/177983418987 : ℝ)*r)*t^2)
  | 4, 4 => (((41486435018725/873736784118 : ℝ) + (-18444671993725/873736784118 : ℝ)*r) + ((-4707732947844250/4805552312649 : ℝ) + (2104329310564400/4805552312649 : ℝ)*r)*t + ((3027125833054000/533950256961 : ℝ) + (-451195878580000/177983418987 : ℝ)*r)*t^2)
  | _, _ => 0


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- `X = B S Bᵗ` entrywise on `range 5`, verified by `linear_combination` against the two
reduction hypotheses. -/
lemma Xm5_eq (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∀ i ∈ range 5, ∀ j ∈ range 5,
      Xm5 r t i j = ∑ p ∈ range 3, ∑ q ∈ range 3, Sm5 r t p q * (Bm5 r p i * Bm5 r q j) := by
  intro i hi j hj
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  interval_cases i <;> interval_cases j <;> simp only [Xm5, Sm5, Bm5]
  case _ => linear_combination -((0:ℝ)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((-45976552450/16180310817 : ℝ) + (11041088966500/177983418987 : ℝ)*t + (-7420212879500/19775935443 : ℝ)*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((-14660350/4052169 : ℝ) + (370213255450/5393436939 : ℝ)*t + (-1978672039000/5393436939 : ℝ)*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((150491882450/16180310817 : ℝ) + (-34299215362850/177983418987 : ℝ)*t + (66286669706000/59327806329 : ℝ)*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((-45976552450/16180310817 : ℝ) + (11041088966500/177983418987 : ℝ)*t + (-7420212879500/19775935443 : ℝ)*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((-45976552450/16180310817 : ℝ) + (11041088966500/177983418987 : ℝ)*t + (-7420212879500/19775935443 : ℝ)*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((-111433397725/32360621634 : ℝ) + (11579356074950/177983418987 : ℝ)*t + (-6768530869000/19775935443 : ℝ)*t^2 + (-653265125/1198541542 : ℝ)*r + (80074454400/6591978481 : ℝ)*r*t + (-491716794000/6591978481 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((-76458782825/32360621634 : ℝ) + (8996429519875/177983418987 : ℝ)*t + (-19123211463500/59327806329 : ℝ)*t^2 + (-509125/900482 : ℝ)*r + (6150966875/599270771 : ℝ)*r*t + (-30892236000/599270771 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((140537992175/32360621634 : ℝ) + (-15275601457075/177983418987 : ℝ)*t + (29265735003500/59327806329 : ℝ)*t^2 + (1984175625/1198541542 : ℝ)*r + (-227809544425/6591978481 : ℝ)*r*t + (1323248184000/6591978481 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((32304936275/32360621634 : ℝ) + (-4376033647750/177983418987 : ℝ)*t + (3209845811000/19775935443 : ℝ)*t^2 + (-653265125/1198541542 : ℝ)*r + (80074454400/6591978481 : ℝ)*r*t + (-491716794000/6591978481 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((-14660350/4052169 : ℝ) + (370213255450/5393436939 : ℝ)*t + (-1978672039000/5393436939 : ℝ)*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((-76458782825/32360621634 : ℝ) + (8996429519875/177983418987 : ℝ)*t + (-19123211463500/59327806329 : ℝ)*t^2 + (-509125/900482 : ℝ)*r + (6150966875/599270771 : ℝ)*r*t + (-30892236000/599270771 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((235193075/44573859 : ℝ) + (-572457376375/5393436939 : ℝ)*t + (3369464860000/5393436939 : ℝ)*t^2 + (-6653800/4952651 : ℝ)*r + (1546134675/54479161 : ℝ)*r*t + (-9514182000/54479161 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((-183651871000/16180310817 : ℝ) + (40741877442925/177983418987 : ℝ)*t + (-26129911739000/19775935443 : ℝ)*t^2 + (12254175/4952651 : ℝ)*r + (-29309415175/599270771 : ℝ)*r*t + (166440474000/599270771 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((170630634475/32360621634 : ℝ) + (-18515807060525/177983418987 : ℝ)*t + (34553890784500/59327806329 : ℝ)*t^2 + (-509125/900482 : ℝ)*r + (6150966875/599270771 : ℝ)*r*t + (-30892236000/599270771 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((150491882450/16180310817 : ℝ) + (-34299215362850/177983418987 : ℝ)*t + (66286669706000/59327806329 : ℝ)*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((140537992175/32360621634 : ℝ) + (-15275601457075/177983418987 : ℝ)*t + (29265735003500/59327806329 : ℝ)*t^2 + (1984175625/1198541542 : ℝ)*r + (-227809544425/6591978481 : ℝ)*r*t + (1323248184000/6591978481 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((-183651871000/16180310817 : ℝ) + (40741877442925/177983418987 : ℝ)*t + (-26129911739000/19775935443 : ℝ)*t^2 + (12254175/4952651 : ℝ)*r + (-29309415175/599270771 : ℝ)*r*t + (166440474000/599270771 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((376637032525/16180310817 : ℝ) + (-83793398016475/177983418987 : ℝ)*t + (160367633242000/59327806329 : ℝ)*t^2 + (-3466930800/599270771 : ℝ)*r + (778022655775/6591978481 : ℝ)*r*t + (-4477341582000/6591978481 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((-394028093125/32360621634 : ℝ) + (44147414568725/177983418987 : ℝ)*t + (-84281627324500/59327806329 : ℝ)*t^2 + (1984175625/1198541542 : ℝ)*r + (-227809544425/6591978481 : ℝ)*r*t + (1323248184000/6591978481 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((-45976552450/16180310817 : ℝ) + (11041088966500/177983418987 : ℝ)*t + (-7420212879500/19775935443 : ℝ)*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((32304936275/32360621634 : ℝ) + (-4376033647750/177983418987 : ℝ)*t + (3209845811000/19775935443 : ℝ)*t^2 + (-653265125/1198541542 : ℝ)*r + (80074454400/6591978481 : ℝ)*r*t + (-491716794000/6591978481 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((170630634475/32360621634 : ℝ) + (-18515807060525/177983418987 : ℝ)*t + (34553890784500/59327806329 : ℝ)*t^2 + (-509125/900482 : ℝ)*r + (6150966875/599270771 : ℝ)*r*t + (-30892236000/599270771 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((-394028093125/32360621634 : ℝ) + (44147414568725/177983418987 : ℝ)*t + (-84281627324500/59327806329 : ℝ)*t^2 + (1984175625/1198541542 : ℝ)*r + (-227809544425/6591978481 : ℝ)*r*t + (1323248184000/6591978481 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3
  case _ => linear_combination -(((176043270275/32360621634 : ℝ) + (-20331423370450/177983418987 : ℝ)*t + (13188222491000/19775935443 : ℝ)*t^2 + (-653265125/1198541542 : ℝ)*r + (80074454400/6591978481 : ℝ)*r*t + (-491716794000/6591978481 : ℝ)*r*t^2)) * hr + -((0:ℝ)) * ht3

/-- **`X` is positive semidefinite.** -/
lemma Xm5_psd {r t : ℝ} (hr2 : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300))
    (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range 5, ∑ j ∈ range 5, Xm5 r t i j * (x i * x j) := by
  have hrw : ∑ i ∈ range 5, ∑ j ∈ range 5, Xm5 r t i j * (x i * x j)
      = ∑ i ∈ range 5, ∑ j ∈ range 5,
          (∑ p ∈ range 3, ∑ q ∈ range 3, Sm5 r t p q * (Bm5 r p i * Bm5 r q j)) * (x i * x j) := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [Xm5_eq r t hr2 ht3 i hi j hj]
  rw [hrw, quadform_transfer]
  exact Sm5_psd_sum hr2 ht3 hr ht (fun p => ∑ i ∈ range 5, Bm5 r p i * x i)





/-! ## The uniform family

The endpoint results above can be made uniform in the line parameter.  Because `z = Bᵗv(s)`
is constant, `h`, `S` and `X` do not depend on `s`, and `v(s) = v(0) + s·d` is affine.  Writing
`A(s) = D(s)⁻¹ G D(s)`, `b(s) = D(s)h`, `R(s) = D(s) X D(s)` with `D(s) = diag v(s)`, the two
identities

  `X G + Gᵀ X = h hᵀ`,      `X v(s) = h`

are all that is needed: the first is `s`-free, the second holds for every `s`, and conjugating
by `D(s)` gives `R(s) e = b(s)` and `M(s) = 0` at every `s` at once — the `v` factors cancel
in `(RA)ᵢⱼ = vᵢ (Σₖ XᵢₖGₖⱼ) vⱼ`. -/

/-- `h`, constant along the segment. -/
noncomputable def hv5 (r t : ℝ) : ℕ → ℝ := fun i =>
  match i with
  | 0 => (((17995465/4384314 : ℝ) + (-7178885/4384314 : ℝ)*r) + ((-189561650/2192157 : ℝ) + (9334720/243573 : ℝ)*r)*t + ((432191600/730719 : ℝ) + (-192750400/730719 : ℝ)*r)*t^2)
  | 1 => (((28818685/4384314 : ℝ) + (-12119345/4384314 : ℝ)*r) + ((-285444050/2192157 : ℝ) + (14174200/243573 : ℝ)*r)*t + ((496916000/730719 : ℝ) + (-221921200/730719 : ℝ)*r)*t^2)
  | 2 => (((-31149395/4384314 : ℝ) + (14177575/4384314 : ℝ)*r) + ((338064250/2192157 : ℝ) + (-16759220/243573 : ℝ)*r)*t + ((-637591600/730719 : ℝ) + (284976800/730719 : ℝ)*r)*t^2)
  | 3 => (((53753725/4384314 : ℝ) + (-24014465/4384314 : ℝ)*r) + ((-573809450/2192157 : ℝ) + (28507360/243573 : ℝ)*r)*t + ((1132182800/730719 : ℝ) + (-506555200/730719 : ℝ)*r)*t^2)
  | 4 => (((-24209855/4384314 : ℝ) + (11236195/4384314 : ℝ)*r) + ((277117150/2192157 : ℝ) + (-13852160/243573 : ℝ)*r)*t + ((-597026800/730719 : ℝ) + (267200000/730719 : ℝ)*r)*t^2)
  | _ => 0

/-- The circulant `G = t·I + u·P + t·P²` on `range 5`. -/
noncomputable def Gm5 (r t : ℝ) : ℕ → ℕ → ℝ := fun i j =>
  match i, j with
  | 0, 0 => ((1 : ℝ)*t)
  | 0, 1 => (((-1/4 : ℝ) + (1/4 : ℝ)*r) + ((3 : ℝ) + (-2 : ℝ)*r)*t)
  | 0, 2 => ((1 : ℝ)*t)
  | 1, 1 => ((1 : ℝ)*t)
  | 1, 2 => (((-1/4 : ℝ) + (1/4 : ℝ)*r) + ((3 : ℝ) + (-2 : ℝ)*r)*t)
  | 1, 3 => ((1 : ℝ)*t)
  | 2, 2 => ((1 : ℝ)*t)
  | 2, 3 => (((-1/4 : ℝ) + (1/4 : ℝ)*r) + ((3 : ℝ) + (-2 : ℝ)*r)*t)
  | 2, 4 => ((1 : ℝ)*t)
  | 3, 0 => ((1 : ℝ)*t)
  | 3, 3 => ((1 : ℝ)*t)
  | 3, 4 => (((-1/4 : ℝ) + (1/4 : ℝ)*r) + ((3 : ℝ) + (-2 : ℝ)*r)*t)
  | 4, 0 => (((-1/4 : ℝ) + (1/4 : ℝ)*r) + ((3 : ℝ) + (-2 : ℝ)*r)*t)
  | 4, 1 => ((1 : ℝ)*t)
  | 4, 4 => ((1 : ℝ)*t)
  | _, _ => 0

/-- `v(s) = v(0) + s·d`, affine in the line parameter. -/
noncomputable def vv5 (r s : ℝ) : ℕ → ℝ := fun i =>
  match i with
  | 0 => 2/5 - (1/2 + r/2)*s
  | 1 => 1 + (1/2 + r/2)*s
  | 2 => 12/5 - s
  | 3 => 21/20
  | 4 => 11/20 + s
  | _ => 0

/-! ### The defining identities of `X`, uniform in `s` -/

/-- Entry `(0,0)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_0_0 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 0 k * Gm5 r t k 0)
      + (∑ k ∈ range 5, Gm5 r t k 0 * Xm5 r t k 0) = hv5 r t 0 * hv5 r t 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((319905850074260/4805552312649 : ℝ) + (-4335017860748050/4805552312649 : ℝ)*t + (-139801501457942000/4805552312649 : ℝ)*t^2 + (22689620555632000/533950256961 : ℝ)*t^3 + (-37152716700160000/533950256961 : ℝ)*t^4) * hr + ((-1059480541300000/26259848703 : ℝ) + (-124184387537120000/177983418987 : ℝ)*t + (473825365856000/26259848703 : ℝ)*r + (166610207553280000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(0,1)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_0_1 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 0 k * Gm5 r t k 1)
      + (∑ k ∈ range 5, Gm5 r t k 0 * Xm5 r t k 1) = hv5 r t 0 * hv5 r t 1 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((-522424903893655/4805552312649 : ℝ) + (21763023467146400/4805552312649 : ℝ)*t + (-206609950915470500/4805552312649 : ℝ)*t^2 + (34649194554556000/533950256961 : ℝ)*t^3 + (-42775400068480000/533950256961 : ℝ)*t^4) * hr + ((1808896546580000/26259848703 : ℝ) + (-142879973816000000/177983418987 : ℝ)*t + (-808963500988000/26259848703 : ℝ)*r + (191693236268320000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(0,2)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_0_2 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 0 k * Gm5 r t k 2)
      + (∑ k ∈ range 5, Gm5 r t k 0 * Xm5 r t k 2) = hv5 r t 0 * hv5 r t 2 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((105759198460130/4805552312649 : ℝ) + (-11001038185761100/4805552312649 : ℝ)*t + (237196583867663500/4805552312649 : ℝ)*t^2 + (-39619034775236000/533950256961 : ℝ)*t^3 + (54929392190720000/533950256961 : ℝ)*t^4) * hr + ((-397326022690000/26259848703 : ℝ) + (183402898234720000/177983418987 : ℝ)*t + (177686183798000/26259848703 : ℝ)*r + (-246060615091520000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(0,3)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_0_3 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 0 k * Gm5 r t k 3)
      + (∑ k ∈ range 5, Gm5 r t k 0 * Xm5 r t k 3) = hv5 r t 0 * hv5 r t 3 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((-69603243714310/4805552312649 : ℝ) + (15942585184523300/4805552312649 : ℝ)*t + (-414306969889451000/4805552312649 : ℝ)*t^2 + (68636501621584000/533950256961 : ℝ)*t^3 + (-97638717422080000/533950256961 : ℝ)*t^4) * hr + ((304032386030000/26259848703 : ℝ) + (-325837827644960000/177983418987 : ℝ)*t + (-135961076386000/26259848703 : ℝ)*r + (437157589949440000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(0,4)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_0_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 0 k * Gm5 r t k 4)
      + (∑ k ∈ range 5, Gm5 r t k 0 * Xm5 r t k 4) = hv5 r t 0 * hv5 r t 4 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((-414607302824575/4805552312649 : ℝ) + (5120764125815450/4805552312649 : ℝ)*t + (196005068139316000/4805552312649 : ℝ)*t^2 + (-32283306538976000/533950256961 : ℝ)*t^3 + (51502906880000000/533950256961 : ℝ)*t^4) * hr + ((1375457600480000/26259848703 : ℝ) + (171848167444960000/177983418987 : ℝ)*t + (-615107926720000/26259848703 : ℝ)*r + (-230558750030720000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(1,1)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_1_1 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 1 k * Gm5 r t k 1)
      + (∑ k ∈ range 5, Gm5 r t k 1 * Xm5 r t k 1) = hv5 r t 1 * hv5 r t 1 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((-943819251312910/4805552312649 : ℝ) + (35312989394596250/4805552312649 : ℝ)*t + (-253996283883349400/4805552312649 : ℝ)*t^2 + (42501294032776000/533950256961 : ℝ)*t^3 + (-49249019009440000/533950256961 : ℝ)*t^4) * hr + ((3257940494300000/26259848703 : ℝ) + (-164390202034400000/177983418987 : ℝ)*t + (-1457006539096000/26259848703 : ℝ)*r + (220552390038400000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(1,2)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_1_2 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 1 k * Gm5 r t k 2)
      + (∑ k ∈ range 5, Gm5 r t k 1 * Xm5 r t k 2) = hv5 r t 1 * hv5 r t 2 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((863604455059535/4805552312649 : ℝ) + (-34898361788720050/4805552312649 : ℝ)*t + (309503639623718200/4805552312649 : ℝ)*t^2 + (-51908234881376000/533950256961 : ℝ)*t^3 + (63242393428160000/533950256961 : ℝ)*t^4) * hr + ((-2987003194330000/26259848703 : ℝ) + (211013811548800000/177983418987 : ℝ)*t + (1335821757146000/26259848703 : ℝ)*r + (-283104624530720000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(1,3)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_1_3 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 1 k * Gm5 r t k 3)
      + (∑ k ∈ range 5, Gm5 r t k 1 * Xm5 r t k 3) = hv5 r t 1 * hv5 r t 3 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((-1641452752755445/4805552312649 : ℝ) + (65198270405629550/4805552312649 : ℝ)*t + (-555142473835378700/4805552312649 : ℝ)*t^2 + (93056504496892000/533950256961 : ℝ)*t^3 + (-112415337850240000/533950256961 : ℝ)*t^4) * hr + ((5668495442870000/26259848703 : ℝ) + (-374892145832000000/177983418987 : ℝ)*t + (-2535021197182000/26259848703 : ℝ)*r + (502970749358560000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(1,4)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_1_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 1 k * Gm5 r t k 4)
      + (∑ k ∈ range 5, Gm5 r t k 1 * Xm5 r t k 4) = hv5 r t 1 * hv5 r t 4 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((603525661960550/4805552312649 : ℝ) + (-26535902053084900/4805552312649 : ℝ)*t + (280354359477757900/4805552312649 : ℝ)*t^2 + (-47121711622868000/533950256961 : ℝ)*t^3 + (59297344640000000/533950256961 : ℝ)*t^4) * hr + ((-2091417572920000/26259848703 : ℝ) + (197719630849600000/177983418987 : ℝ)*t + (935321302340000/26259848703 : ℝ)*r + (-265268859088160000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(2,2)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_2_2 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 2 k * Gm5 r t k 2)
      + (∑ k ∈ range 5, Gm5 r t k 2 * Xm5 r t k 2) = hv5 r t 2 * hv5 r t 2 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((-572436160886560/4805552312649 : ℝ) + (28738398543381650/4805552312649 : ℝ)*t + (-371424423492638600/4805552312649 : ℝ)*t^2 + (62359875903976000/533950256961 : ℝ)*t^3 + (-81211776538240000/533950256961 : ℝ)*t^4) * hr + ((2001154747280000/26259848703 : ℝ) + (-270860643693920000/177983418987 : ℝ)*t + (-894946170196000/26259848703 : ℝ)*r + (363397627749760000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(2,3)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_2_3 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 2 k * Gm5 r t k 3)
      + (∑ k ∈ range 5, Gm5 r t k 2 * Xm5 r t k 3) = hv5 r t 2 * hv5 r t 3 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((995275020852320/4805552312649 : ℝ) + (-50377301882896750/4805552312649 : ℝ)*t + (658364918943684100/4805552312649 : ℝ)*t^2 + (-110313471274724000/533950256961 : ℝ)*t^3 + (144356479919360000/533950256961 : ℝ)*t^4) * hr + ((-3480166870240000/26259848703 : ℝ) + (481217547513760000/177983418987 : ℝ)*t + (1556381190932000/26259848703 : ℝ)*r + (-645621171815360000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(2,4)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_2_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 2 k * Gm5 r t k 4)
      + (∑ k ∈ range 5, Gm5 r t k 2 * Xm5 r t k 4) = hv5 r t 2 * hv5 r t 4 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((-104452767666625/4805552312649 : ℝ) + (13982649895226000/4805552312649 : ℝ)*t + (-326902822449505700/4805552312649 : ℝ)*t^2 + (54849329825740000/533950256961 : ℝ)*t^3 + (-76145800960000000/533950256961 : ℝ)*t^4) * hr + ((400654399730000/26259848703 : ℝ) + (-253796092484960000/177983418987 : ℝ)*t + (-179175371050000/26259848703 : ℝ)*r + (340503262498240000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(3,3)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_3_3 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 3 k * Gm5 r t k 3)
      + (∑ k ∈ range 5, Gm5 r t k 3 * Xm5 r t k 3) = hv5 r t 3 * hv5 r t 3 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((-1702691151783340/4805552312649 : ℝ) + (87453084213862850/4805552312649 : ℝ)*t + (-1164885195419873600/4805552312649 : ℝ)*t^2 + (194454427963696000/533950256961 : ℝ)*t^3 + (-256598170647040000/533950256961 : ℝ)*t^4) * hr + ((5958207199760000/26259848703 : ℝ) + (-854942915283680000/177983418987 : ℝ)*t + (-2664591038884000/26259848703 : ℝ)*r + (1147026169381120000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(3,4)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_3_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 3 k * Gm5 r t k 4)
      + (∑ k ∈ range 5, Gm5 r t k 3 * Xm5 r t k 4) = hv5 r t 3 * hv5 r t 4 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((24493554001175/4805552312649 : ℝ) + (-19959353989331200/4805552312649 : ℝ)*t + (571614145884902200/4805552312649 : ℝ)*t^2 + (-95370265746848000/533950256961 : ℝ)*t^3 + (135351549440000000/533950256961 : ℝ)*t^4) * hr + ((-2700788470000/430489323 : ℝ) + (450900407099680000/177983418987 : ℝ)*t + (1207864310000/430489323 : ℝ)*r + (-604946274239360000/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(4,4)` of `X G + Gᵗ X = h hᵗ`. -/
lemma XGid5_4_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, Xm5 r t 4 k * Gm5 r t k 4)
      + (∑ k ∈ range 5, Gm5 r t k 4 * Xm5 r t k 4) = hv5 r t 4 * hv5 r t 4 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Xm5, Gm5, hv5]
  linear_combination ((524485488534350/4805552312649 : ℝ) + (-5571371645409850/4805552312649 : ℝ)*t + (-274913322206968400/4805552312649 : ℝ)*t^2 + (45756049732432000/533950256961 : ℝ)*t^3 + (-71395840000000000/533950256961 : ℝ)*t^4) * hr + ((-1741981086220000/26259848703 : ℝ) + (-237806733306080000/177983418987 : ℝ)*t + (779047601120000/26259848703 : ℝ)*r + (319051121920000000/533950256961 : ℝ)*r*t) * ht3

/-! ### `X v(s) = h`, for every `s` -/

lemma Xv5_eq_h (r t s : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∀ i ∈ range 5, (∑ j ∈ range 5, Xm5 r t i j * vv5 r s j) = hv5 r t i := by
  intro i hi
  have hi' := mem_range.1 hi
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  interval_cases i <;> simp only [Xm5, vv5, hv5]
  case _ => linear_combination ((0:ℝ) + (((62435739650/16180310817 : ℝ) + (-5566746197300/59327806329 : ℝ)*t + (36517108913000/59327806329 : ℝ)*t^2))*s) * hr
    + ((0:ℝ) + ((0:ℝ))*s) * ht3
  case _ => linear_combination ((0:ℝ) + (((-7119727150/16180310817 : ℝ) + (1306706599300/59327806329 : ℝ)*t + (-12844507735000/59327806329 : ℝ)*t^2))*s) * hr
    + ((0:ℝ) + ((0:ℝ))*s) * ht3
  case _ => linear_combination ((0:ℝ) + (((-27956850250/16180310817 : ℝ) + (1812022330900/59327806329 : ℝ)*t + (-7027572007000/59327806329 : ℝ)*t^2))*s) * hr
    + ((0:ℝ) + ((0:ℝ))*s) * ht3
  case _ => linear_combination ((0:ℝ) + (((75781016150/16180310817 : ℝ) + (-5879711385500/59327806329 : ℝ)*t + (32920634177000/59327806329 : ℝ)*t^2))*s) * hr
    + ((0:ℝ) + ((0:ℝ))*s) * ht3
  case _ => linear_combination ((0:ℝ) + (((-71717416150/16180310817 : ℝ) + (6062215584100/59327806329 : ℝ)*t + (-37540058383000/59327806329 : ℝ)*t^2))*s) * hr
    + ((0:ℝ) + ((0:ℝ))*s) * ht3

/-! ### The transported tableau, uniform in `s` -/

/-- `A(s) = D(s)⁻¹ G D(s)`. -/
noncomputable def Au (r t s : ℝ) : ℕ → ℕ → ℝ := fun i j => Gm5 r t i j * vv5 r s j / vv5 r s i
/-- `b(s) = D(s) h`. -/
noncomputable def bu (r t s : ℝ) : ℕ → ℝ := fun i => vv5 r s i * hv5 r t i
/-- `R(s) = D(s) X D(s)`. -/
noncomputable def Ru (r t s : ℝ) : ℕ → ℕ → ℝ := fun i j => vv5 r s i * Xm5 r t i j * vv5 r s j
/-- `c(s) = A(s) e`. -/
noncomputable def cu (r t s : ℝ) : ℕ → ℝ := fun i =>
  (∑ j ∈ range 5, Gm5 r t i j * vv5 r s j) / vv5 r s i

/-- `c = A e` uniformly. -/
lemma cu_rowsum (r t s : ℝ) : ∀ i ∈ range 5, cu r t s i = ∑ j ∈ range 5, Au r t s i j := by
  intro i _
  unfold cu Au
  rw [← Finset.sum_div]

/-- `R e = b` uniformly, transported from `X v = h`. -/
lemma Ru_rowsum (r t s : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∀ i ∈ range 5, ∑ j ∈ range 5, Ru r t s i j = bu r t s i := by
  intro i hi
  unfold Ru bu
  have h : ∑ j ∈ range 5, vv5 r s i * Xm5 r t i j * vv5 r s j
      = vv5 r s i * ∑ j ∈ range 5, Xm5 r t i j * vv5 r s j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [h, Xv5_eq_h r t s hr ht3 i hi]

/-- `R` symmetric uniformly. -/
lemma Ru_symm (r t s : ℝ) : ∀ i ∈ range 5, ∀ j ∈ range 5, Ru r t s i j = Ru r t s j i := by
  intro i hi j hj
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  unfold Ru
  have hsym : Xm5 r t i j = Xm5 r t j i := by
    interval_cases i <;> interval_cases j <;> simp [Xm5]
  rw [hsym]; ring



set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- `X G + Gᵗ X = h hᵗ` on all of `range 5 × range 5` (not just the upper triangle). -/
lemma XG5_full (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∀ i ∈ range 5, ∀ j ∈ range 5,
      (∑ k ∈ range 5, Xm5 r t i k * Gm5 r t k j)
        + (∑ k ∈ range 5, Gm5 r t k i * Xm5 r t k j) = hv5 r t i * hv5 r t j := by
  intro i hi j hj
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  interval_cases i <;> interval_cases j <;> simp only [Xm5, Gm5, hv5]
  case _ => linear_combination ((319905850074260/4805552312649 : ℝ) + (-4335017860748050/4805552312649 : ℝ)*t + (-139801501457942000/4805552312649 : ℝ)*t^2 + (22689620555632000/533950256961 : ℝ)*t^3 + (-37152716700160000/533950256961 : ℝ)*t^4) * hr + ((-1059480541300000/26259848703 : ℝ) + (-124184387537120000/177983418987 : ℝ)*t + (473825365856000/26259848703 : ℝ)*r + (166610207553280000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((-522424903893655/4805552312649 : ℝ) + (21763023467146400/4805552312649 : ℝ)*t + (-206609950915470500/4805552312649 : ℝ)*t^2 + (34649194554556000/533950256961 : ℝ)*t^3 + (-42775400068480000/533950256961 : ℝ)*t^4) * hr + ((1808896546580000/26259848703 : ℝ) + (-142879973816000000/177983418987 : ℝ)*t + (-808963500988000/26259848703 : ℝ)*r + (191693236268320000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((105759198460130/4805552312649 : ℝ) + (-11001038185761100/4805552312649 : ℝ)*t + (237196583867663500/4805552312649 : ℝ)*t^2 + (-39619034775236000/533950256961 : ℝ)*t^3 + (54929392190720000/533950256961 : ℝ)*t^4) * hr + ((-397326022690000/26259848703 : ℝ) + (183402898234720000/177983418987 : ℝ)*t + (177686183798000/26259848703 : ℝ)*r + (-246060615091520000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((-69603243714310/4805552312649 : ℝ) + (15942585184523300/4805552312649 : ℝ)*t + (-414306969889451000/4805552312649 : ℝ)*t^2 + (68636501621584000/533950256961 : ℝ)*t^3 + (-97638717422080000/533950256961 : ℝ)*t^4) * hr + ((304032386030000/26259848703 : ℝ) + (-325837827644960000/177983418987 : ℝ)*t + (-135961076386000/26259848703 : ℝ)*r + (437157589949440000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((-414607302824575/4805552312649 : ℝ) + (5120764125815450/4805552312649 : ℝ)*t + (196005068139316000/4805552312649 : ℝ)*t^2 + (-32283306538976000/533950256961 : ℝ)*t^3 + (51502906880000000/533950256961 : ℝ)*t^4) * hr + ((1375457600480000/26259848703 : ℝ) + (171848167444960000/177983418987 : ℝ)*t + (-615107926720000/26259848703 : ℝ)*r + (-230558750030720000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((-522424903893655/4805552312649 : ℝ) + (21763023467146400/4805552312649 : ℝ)*t + (-206609950915470500/4805552312649 : ℝ)*t^2 + (34649194554556000/533950256961 : ℝ)*t^3 + (-42775400068480000/533950256961 : ℝ)*t^4) * hr + ((1808896546580000/26259848703 : ℝ) + (-142879973816000000/177983418987 : ℝ)*t + (-808963500988000/26259848703 : ℝ)*r + (191693236268320000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((-943819251312910/4805552312649 : ℝ) + (35312989394596250/4805552312649 : ℝ)*t + (-253996283883349400/4805552312649 : ℝ)*t^2 + (42501294032776000/533950256961 : ℝ)*t^3 + (-49249019009440000/533950256961 : ℝ)*t^4) * hr + ((3257940494300000/26259848703 : ℝ) + (-164390202034400000/177983418987 : ℝ)*t + (-1457006539096000/26259848703 : ℝ)*r + (220552390038400000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((863604455059535/4805552312649 : ℝ) + (-34898361788720050/4805552312649 : ℝ)*t + (309503639623718200/4805552312649 : ℝ)*t^2 + (-51908234881376000/533950256961 : ℝ)*t^3 + (63242393428160000/533950256961 : ℝ)*t^4) * hr + ((-2987003194330000/26259848703 : ℝ) + (211013811548800000/177983418987 : ℝ)*t + (1335821757146000/26259848703 : ℝ)*r + (-283104624530720000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((-1641452752755445/4805552312649 : ℝ) + (65198270405629550/4805552312649 : ℝ)*t + (-555142473835378700/4805552312649 : ℝ)*t^2 + (93056504496892000/533950256961 : ℝ)*t^3 + (-112415337850240000/533950256961 : ℝ)*t^4) * hr + ((5668495442870000/26259848703 : ℝ) + (-374892145832000000/177983418987 : ℝ)*t + (-2535021197182000/26259848703 : ℝ)*r + (502970749358560000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((603525661960550/4805552312649 : ℝ) + (-26535902053084900/4805552312649 : ℝ)*t + (280354359477757900/4805552312649 : ℝ)*t^2 + (-47121711622868000/533950256961 : ℝ)*t^3 + (59297344640000000/533950256961 : ℝ)*t^4) * hr + ((-2091417572920000/26259848703 : ℝ) + (197719630849600000/177983418987 : ℝ)*t + (935321302340000/26259848703 : ℝ)*r + (-265268859088160000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((105759198460130/4805552312649 : ℝ) + (-11001038185761100/4805552312649 : ℝ)*t + (237196583867663500/4805552312649 : ℝ)*t^2 + (-39619034775236000/533950256961 : ℝ)*t^3 + (54929392190720000/533950256961 : ℝ)*t^4) * hr + ((-397326022690000/26259848703 : ℝ) + (183402898234720000/177983418987 : ℝ)*t + (177686183798000/26259848703 : ℝ)*r + (-246060615091520000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((863604455059535/4805552312649 : ℝ) + (-34898361788720050/4805552312649 : ℝ)*t + (309503639623718200/4805552312649 : ℝ)*t^2 + (-51908234881376000/533950256961 : ℝ)*t^3 + (63242393428160000/533950256961 : ℝ)*t^4) * hr + ((-2987003194330000/26259848703 : ℝ) + (211013811548800000/177983418987 : ℝ)*t + (1335821757146000/26259848703 : ℝ)*r + (-283104624530720000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((-572436160886560/4805552312649 : ℝ) + (28738398543381650/4805552312649 : ℝ)*t + (-371424423492638600/4805552312649 : ℝ)*t^2 + (62359875903976000/533950256961 : ℝ)*t^3 + (-81211776538240000/533950256961 : ℝ)*t^4) * hr + ((2001154747280000/26259848703 : ℝ) + (-270860643693920000/177983418987 : ℝ)*t + (-894946170196000/26259848703 : ℝ)*r + (363397627749760000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((995275020852320/4805552312649 : ℝ) + (-50377301882896750/4805552312649 : ℝ)*t + (658364918943684100/4805552312649 : ℝ)*t^2 + (-110313471274724000/533950256961 : ℝ)*t^3 + (144356479919360000/533950256961 : ℝ)*t^4) * hr + ((-3480166870240000/26259848703 : ℝ) + (481217547513760000/177983418987 : ℝ)*t + (1556381190932000/26259848703 : ℝ)*r + (-645621171815360000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((-104452767666625/4805552312649 : ℝ) + (13982649895226000/4805552312649 : ℝ)*t + (-326902822449505700/4805552312649 : ℝ)*t^2 + (54849329825740000/533950256961 : ℝ)*t^3 + (-76145800960000000/533950256961 : ℝ)*t^4) * hr + ((400654399730000/26259848703 : ℝ) + (-253796092484960000/177983418987 : ℝ)*t + (-179175371050000/26259848703 : ℝ)*r + (340503262498240000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((-69603243714310/4805552312649 : ℝ) + (15942585184523300/4805552312649 : ℝ)*t + (-414306969889451000/4805552312649 : ℝ)*t^2 + (68636501621584000/533950256961 : ℝ)*t^3 + (-97638717422080000/533950256961 : ℝ)*t^4) * hr + ((304032386030000/26259848703 : ℝ) + (-325837827644960000/177983418987 : ℝ)*t + (-135961076386000/26259848703 : ℝ)*r + (437157589949440000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((-1641452752755445/4805552312649 : ℝ) + (65198270405629550/4805552312649 : ℝ)*t + (-555142473835378700/4805552312649 : ℝ)*t^2 + (93056504496892000/533950256961 : ℝ)*t^3 + (-112415337850240000/533950256961 : ℝ)*t^4) * hr + ((5668495442870000/26259848703 : ℝ) + (-374892145832000000/177983418987 : ℝ)*t + (-2535021197182000/26259848703 : ℝ)*r + (502970749358560000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((995275020852320/4805552312649 : ℝ) + (-50377301882896750/4805552312649 : ℝ)*t + (658364918943684100/4805552312649 : ℝ)*t^2 + (-110313471274724000/533950256961 : ℝ)*t^3 + (144356479919360000/533950256961 : ℝ)*t^4) * hr + ((-3480166870240000/26259848703 : ℝ) + (481217547513760000/177983418987 : ℝ)*t + (1556381190932000/26259848703 : ℝ)*r + (-645621171815360000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((-1702691151783340/4805552312649 : ℝ) + (87453084213862850/4805552312649 : ℝ)*t + (-1164885195419873600/4805552312649 : ℝ)*t^2 + (194454427963696000/533950256961 : ℝ)*t^3 + (-256598170647040000/533950256961 : ℝ)*t^4) * hr + ((5958207199760000/26259848703 : ℝ) + (-854942915283680000/177983418987 : ℝ)*t + (-2664591038884000/26259848703 : ℝ)*r + (1147026169381120000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((24493554001175/4805552312649 : ℝ) + (-19959353989331200/4805552312649 : ℝ)*t + (571614145884902200/4805552312649 : ℝ)*t^2 + (-95370265746848000/533950256961 : ℝ)*t^3 + (135351549440000000/533950256961 : ℝ)*t^4) * hr + ((-2700788470000/430489323 : ℝ) + (450900407099680000/177983418987 : ℝ)*t + (1207864310000/430489323 : ℝ)*r + (-604946274239360000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((-414607302824575/4805552312649 : ℝ) + (5120764125815450/4805552312649 : ℝ)*t + (196005068139316000/4805552312649 : ℝ)*t^2 + (-32283306538976000/533950256961 : ℝ)*t^3 + (51502906880000000/533950256961 : ℝ)*t^4) * hr + ((1375457600480000/26259848703 : ℝ) + (171848167444960000/177983418987 : ℝ)*t + (-615107926720000/26259848703 : ℝ)*r + (-230558750030720000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((603525661960550/4805552312649 : ℝ) + (-26535902053084900/4805552312649 : ℝ)*t + (280354359477757900/4805552312649 : ℝ)*t^2 + (-47121711622868000/533950256961 : ℝ)*t^3 + (59297344640000000/533950256961 : ℝ)*t^4) * hr + ((-2091417572920000/26259848703 : ℝ) + (197719630849600000/177983418987 : ℝ)*t + (935321302340000/26259848703 : ℝ)*r + (-265268859088160000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((-104452767666625/4805552312649 : ℝ) + (13982649895226000/4805552312649 : ℝ)*t + (-326902822449505700/4805552312649 : ℝ)*t^2 + (54849329825740000/533950256961 : ℝ)*t^3 + (-76145800960000000/533950256961 : ℝ)*t^4) * hr + ((400654399730000/26259848703 : ℝ) + (-253796092484960000/177983418987 : ℝ)*t + (-179175371050000/26259848703 : ℝ)*r + (340503262498240000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((24493554001175/4805552312649 : ℝ) + (-19959353989331200/4805552312649 : ℝ)*t + (571614145884902200/4805552312649 : ℝ)*t^2 + (-95370265746848000/533950256961 : ℝ)*t^3 + (135351549440000000/533950256961 : ℝ)*t^4) * hr + ((-2700788470000/430489323 : ℝ) + (450900407099680000/177983418987 : ℝ)*t + (1207864310000/430489323 : ℝ)*r + (-604946274239360000/533950256961 : ℝ)*r*t) * ht3
  case _ => linear_combination ((524485488534350/4805552312649 : ℝ) + (-5571371645409850/4805552312649 : ℝ)*t + (-274913322206968400/4805552312649 : ℝ)*t^2 + (45756049732432000/533950256961 : ℝ)*t^3 + (-71395840000000000/533950256961 : ℝ)*t^4) * hr + ((-1741981086220000/26259848703 : ℝ) + (-237806733306080000/177983418987 : ℝ)*t + (779047601120000/26259848703 : ℝ)*r + (319051121920000000/533950256961 : ℝ)*r*t) * ht3

/-- **`M(s) = 0` for every `s`**, transported by conjugation with `D(s)`. -/
lemma Mu_zero (r t s : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300))
    (hv : ∀ i ∈ range 5, vv5 r s i ≠ 0) :
    ∀ i ∈ range 5, ∀ j ∈ range 5,
      (∑ k ∈ range 5, Ru r t s i k * Au r t s k j)
        + (∑ k ∈ range 5, Ru r t s j k * Au r t s k i)
        - bu r t s i * bu r t s j = 0 := by
  intro i hi j hj
  have key : ∀ p q : ℕ, q ∈ range 5 →
      ∑ k ∈ range 5, Ru r t s p k * Au r t s k q
        = vv5 r s p * (∑ k ∈ range 5, Xm5 r t p k * Gm5 r t k q) * vv5 r s q := by
    intro p q _
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hvk := hv k hk
    unfold Ru Au
    field_simp
  rw [key i j hj, key j i hi]
  unfold bu
  have hsym : ∑ k ∈ range 5, Xm5 r t j k * Gm5 r t k i
      = ∑ k ∈ range 5, Gm5 r t k i * Xm5 r t k j := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hj' := mem_range.1 hj
    have hk' := mem_range.1 hk
    have hx : Xm5 r t j k = Xm5 r t k j := by
      interval_cases j <;> interval_cases k <;> simp [Xm5]
    rw [hx, mul_comm]
  rw [hsym]
  have h1 := XG5_full r t hr ht3 i hi j hj
  linear_combination (vv5 r s i * vv5 r s j) * h1




/-- **`R(s)` is positive semidefinite for every `s`.** -/
theorem Ru_psd {r t : ℝ} (hr2 : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300))
    (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) (s : ℝ) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range 5, ∑ j ∈ range 5, Ru r t s i j * (x i * x j) := by
  have hrw : ∑ i ∈ range 5, ∑ j ∈ range 5, Ru r t s i j * (x i * x j)
      = ∑ i ∈ range 5, ∑ j ∈ range 5,
          Xm5 r t i j * ((vv5 r s i * x i) * (vv5 r s j * x j)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    unfold Ru; ring
  rw [hrw]
  exact Xm5_psd hr2 ht3 hr ht (fun i => vv5 r s i * x i)

/-- `v(s) > 0` on the segment `s ∈ [-1/50, 0]`. -/
lemma vv5_pos {r s : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (hs : s ∈ Set.Icc (-1/50 : ℝ) 0) : ∀ i ∈ range 5, 0 < vv5 r s i := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨hs1, hs2⟩ := hs
  intro i hi
  have hi' := mem_range.1 hi
  interval_cases i <;> simp only [vv5] <;> nlinarith [hr1, hr2, hs1, hs2]




/-- `h > 0` on the two brackets. -/
lemma hv5_pos {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) :
    ∀ i ∈ range 5, 0 < hv5 r t i := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  intro i hi
  have hi' := mem_range.1 hi
  interval_cases i <;> simp only [hv5] <;> nlinarith [hr1, hr2, ht1, ht2]

/-- **`b(s) > 0` for every `s` in the segment**, from `v(s) > 0` and `h > 0`. -/
lemma bu_pos {r t s : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000))
    (hs : s ∈ Set.Icc (-1/50 : ℝ) 0) : ∀ i ∈ range 5, 0 < bu r t s i := by
  intro i hi
  have h1 := vv5_pos hr hs i hi
  have h2 := hv5_pos hr ht i hi
  unfold bu
  positivity

/-- `G ≥ 0` entrywise, hence `A(s) ≥ 0`. -/
lemma Gm5_nonneg {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) :
    ∀ i ∈ range 5, ∀ j ∈ range 5, 0 ≤ Gm5 r t i j := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  intro i hi j hj
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  interval_cases i <;> interval_cases j <;> simp only [Gm5] <;> nlinarith [hr1, hr2, ht1, ht2]

/-- **`A(s) ≥ 0` entrywise for every `s`.** -/
lemma Au_nonneg {r t s : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000))
    (hs : s ∈ Set.Icc (-1/50 : ℝ) 0) :
    ∀ i ∈ range 5, ∀ j ∈ range 5, 0 ≤ Au r t s i j := by
  intro i hi j hj
  have hvi := vv5_pos hr hs i hi
  have hvj := vv5_pos hr hs j hj
  have hg := Gm5_nonneg hr ht i hi j hj
  unfold Au
  positivity




set_option maxHeartbeats 2000000 in
/-- **`c(s) ⊂ (0,1)` for every `s` in the segment.** -/
lemma cu_mem {r t s : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000))
    (hs : s ∈ Set.Icc (-1/50 : ℝ) 0) :
    ∀ i ∈ range 5, 0 < cu r t s i ∧ cu r t s i < 1 := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨hs1, hs2⟩ := hs
  intro i hi
  have hi' := mem_range.1 hi
  have hv := vv5_pos ⟨hr1, hr2⟩ ⟨hs1, hs2⟩ i hi
  have p1 : 0 ≤ (s + 1/50) * (r - 2236067/1000000) := by
    apply mul_nonneg <;> linarith
  have p2 : 0 ≤ (-s) * (r - 2236067/1000000) := by
    apply mul_nonneg <;> linarith
  have p3 : 0 ≤ (-s) * (t - 35127/1000000) := by
    apply mul_nonneg <;> linarith
  have p4 : 0 ≤ (-s) * (35128/1000000 - t) := by
    apply mul_nonneg <;> linarith
  have p5 : 0 ≤ (s + 1/50) * (2236068/1000000 - r) := by
    apply mul_nonneg <;> linarith
  have p6 : 0 ≤ (s + 1/50) * (t - 35127/1000000) := by
    apply mul_nonneg <;> linarith
  have p7 : 0 ≤ (-s) * (r - 2236067/1000000) * (t - 35127/1000000) := by
    apply mul_nonneg (by apply mul_nonneg <;> linarith) (by linarith)
  have p8 : 0 ≤ (s + 1/50) * (r - 2236067/1000000) * (t - 35127/1000000) := by
    apply mul_nonneg (by apply mul_nonneg <;> linarith) (by linarith)
  unfold cu
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  interval_cases i <;> simp only [Gm5, vv5] at hv ⊢ <;>
    refine ⟨div_pos (by nlinarith [p1,p2,p3,p4,p5,p6,p7,p8]) (by nlinarith [p1,p2,p5]), ?_⟩ <;>
      rw [div_lt_one (by nlinarith [p1,p2,p5])] <;>
      nlinarith [p1,p2,p3,p4,p5,p6,p7,p8]

set_option maxHeartbeats 4000000 in
/-- Separating bounds for the abscissas, uniform in `s`: each `cᵢ` is trapped between two
rationals, and the five intervals are disjoint and increasing along `perm5`. -/
lemma cu_bounds {r t s : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000))
    (hs : s ∈ Set.Icc (-1/50 : ℝ) 0) :
    cu r t s 2 < 16/100 ∧ 16/100 < cu r t s 3 ∧ cu r t s 3 < 24/100
      ∧ 24/100 < cu r t s 4 ∧ cu r t s 4 < 1/2
      ∧ 1/2 < cu r t s 1 ∧ cu r t s 1 < 76/100 ∧ 76/100 < cu r t s 0 := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨hs1, hs2⟩ := hs
  have h0 : (0:ℝ) < 2/5 - (1/2 + r/2)*s := by nlinarith
  have h1 : (0:ℝ) < 1 + (1/2 + r/2)*s := by nlinarith
  have h2 : (0:ℝ) < 12/5 - s := by linarith
  have h4 : (0:ℝ) < 11/20 + s := by linarith
  have p1 : 0 ≤ (s + 1/50) * (r - 2236067/1000000) := by apply mul_nonneg <;> linarith
  have p2 : 0 ≤ (-s) * (r - 2236067/1000000) := by apply mul_nonneg <;> linarith
  have p3 : 0 ≤ (-s) * (t - 35127/1000000) := by apply mul_nonneg <;> linarith
  have p4 : 0 ≤ (s + 1/50) * (t - 35127/1000000) := by apply mul_nonneg <;> linarith
  have p5 : 0 ≤ (-s) * (35128/1000000 - t) := by apply mul_nonneg <;> linarith
  have p6 : 0 ≤ (s + 1/50) * (2236068/1000000 - r) := by apply mul_nonneg <;> linarith
  have p7 : 0 ≤ (-s) * (s + 1/50) := by apply mul_nonneg <;> linarith
  have p8 : 0 ≤ (-s) * (r - 2236067/1000000) * (t - 35127/1000000) := by
    apply mul_nonneg (by apply mul_nonneg <;> linarith) (by linarith)
  unfold cu
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, Gm5, vv5]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (rw [div_lt_iff₀ (by nlinarith)]; nlinarith [p1,p2,p3,p4,p5,p6,p7,p8])
      | (rw [lt_div_iff₀ (by nlinarith)]; nlinarith [p1,p2,p3,p4,p5,p6,p7,p8])



/-- **The abscissas are strictly ordered by `perm5`, uniformly in `s`** — immediate from the
separating bounds, since the five intervals are disjoint and increasing. -/
lemma cu_sorted {r t s : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000))
    (hs : s ∈ Set.Icc (-1/50 : ℝ) 0) :
    ∀ i ∈ range 5, ∀ j ∈ range 5, i < j → cu r t s (perm5 i) < cu r t s (perm5 j) := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := cu_bounds hr ht hs
  intro i hi j hj hij
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  interval_cases i <;> interval_cases j <;> simp only [perm5] <;>
    first
      | exact absurd hij (by omega)
      | linarith




/-- **`bᵀe = 1` for every `s`.** -/
lemma m0_u (r t s : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∑ i ∈ range 5, bu r t s i = 1 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    bu, vv5, hv5]
  linear_combination ((0:ℝ) + (((-45745/81191 : ℝ) + (806580/81191 : ℝ)*t + (-1620600/81191 : ℝ)*t^2))*s) * hr + ((0:ℝ) + ((0:ℝ))*s) * ht3



/-- `bᵢcᵢ = hᵢ(Gv)ᵢ` termwise, so the `v` cancels. -/
lemma bu_cu_term (r t s : ℝ) (hv : ∀ i ∈ range 5, vv5 r s i ≠ 0) :
    ∀ i ∈ range 5, bu r t s i * cu r t s i
      = hv5 r t i * ∑ j ∈ range 5, Gm5 r t i j * vv5 r s j := by
  intro i hi
  have h := hv i hi
  unfold bu cu
  field_simp

/-- **`bᵀc = 1/2` for every `s`.** -/
lemma m1_u (r t s : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300))
    (hv : ∀ i ∈ range 5, vv5 r s i ≠ 0) :
    ∑ i ∈ range 5, bu r t s i * cu r t s i = 1/2 := by
  rw [Finset.sum_congr rfl (bu_cu_term r t s hv)]
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Gm5, vv5, hv5]
  linear_combination (((-10683/440 : ℝ) + (32009/44 : ℝ)*t + (-12938/11 : ℝ)*t^2 + (18000/11 : ℝ)*t^3) + (((85255/162382 : ℝ) + (-1197000/81191 : ℝ)*t + (11728300/81191 : ℝ)*t^2 + (-35292600/81191 : ℝ)*t^3 + (-85255/162382 : ℝ)*r + (1307140/81191 : ℝ)*r*t + (-14117160/81191 : ℝ)*r*t^2 + (51105600/81191 : ℝ)*r*t^3))*s) * hr + (((166500/11 : ℝ) + (-74460/11 : ℝ)*r) + ((0:ℝ))*s) * ht3

/-- `bᵢ(Ac)ᵢ = hᵢ(G²v)ᵢ` termwise. -/
lemma bu_Auc_term (r t s : ℝ) (hv : ∀ i ∈ range 5, vv5 r s i ≠ 0) :
    ∀ i ∈ range 5, bu r t s i * (∑ j ∈ range 5, Au r t s i j * cu r t s j)
      = hv5 r t i * ∑ j ∈ range 5, Gm5 r t i j * (∑ k ∈ range 5, Gm5 r t j k * vv5 r s k) := by
  intro i hi
  have hi0 := hv i hi
  unfold bu Au cu
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 := hv j hj
  field_simp

/-- **`bᵀAc = 1/6` for every `s`.** -/
lemma m2_u (r t s : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300))
    (hv : ∀ i ∈ range 5, vv5 r s i ≠ 0) :
    ∑ i ∈ range 5, bu r t s i * (∑ j ∈ range 5, Au r t s i j * cu r t s j) = 1/6 := by
  rw [Finset.sum_congr rfl (bu_Auc_term r t s hv)]
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    Gm5, vv5, hv5]
  linear_combination (((72829/5280 : ℝ) + (-106393/176 : ℝ)*t + (287125/44 : ℝ)*t^2 + (-128690/11 : ℝ)*t^3 + (190320/11 : ℝ)*t^4 + (-103/352 : ℝ)*r + (1981/176 : ℝ)*r*t + (-7237/44 : ℝ)*r*t^2 + (11768/11 : ℝ)*r*t^3 + (-28560/11 : ℝ)*r*t^4) + (((326395/1299056 : ℝ) + (-1337535/162382 : ℝ)*t + (8215325/81191 : ℝ)*t^2 + (-43270850/81191 : ℝ)*t^3 + (82230000/81191 : ℝ)*t^4 + (-326395/649528 : ℝ)*r + (261165/14762 : ℝ)*r*t + (-19138825/81191 : ℝ)*r*t^2 + (111786000/81191 : ℝ)*r*t^3 + (-237729600/81191 : ℝ)*r*t^4 + (326395/1299056 : ℝ)*r^2 + (-767640/81191 : ℝ)*r^2*t + (11052150/81191 : ℝ)*r^2*t^2 + (-71226080/81191 : ℝ)*r^2*t^3 + (171945600/81191 : ℝ)*r^2*t^4))*s) * hr + (((-91825/11 : ℝ) + (1292700/11 : ℝ)*t + (41065/11 : ℝ)*r + (-578100/11 : ℝ)*r*t) + ((0:ℝ))*s) * ht3


/-- **All eleven structural conditions of the Claim, uniformly in the line parameter.**

For every `r`, `t` in the two brackets with `r² = 5` and the cubic reduction, and every
`s ∈ [−1/50, 0]`, the transported tableau satisfies `A ≥ 0`, `b > 0`, `c = A e` strictly
ordered by `perm5` inside `(0,1)`, `R` symmetric positive semidefinite with `R e = b`,
`M = 0`, and the three order conditions `bᵀe = 1`, `bᵀc = 1/2`, `bᵀAc = 1/6`.

Only `bᵀc² = 1/3` is missing, and that is what the sign change supplies at an interior `s`. -/
theorem five_uniform {r t s : ℝ}
    (hr2 : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300))
    (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000))
    (hs : s ∈ Set.Icc (-1/50 : ℝ) 0) :
    (∀ i ∈ range 5, ∀ j ∈ range 5, 0 ≤ Au r t s i j)
      ∧ (∀ i ∈ range 5, 0 < bu r t s i)
      ∧ (∀ i ∈ range 5, cu r t s i = ∑ j ∈ range 5, Au r t s i j)
      ∧ (∀ i ∈ range 5, 0 < cu r t s i ∧ cu r t s i < 1)
      ∧ (∀ i ∈ range 5, ∀ j ∈ range 5, i < j → cu r t s (perm5 i) < cu r t s (perm5 j))
      ∧ (∀ i ∈ range 5, ∀ j ∈ range 5, Ru r t s i j = Ru r t s j i)
      ∧ (∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 5, ∑ j ∈ range 5, Ru r t s i j * (x i * x j))
      ∧ (∀ i ∈ range 5, ∑ j ∈ range 5, Ru r t s i j = bu r t s i)
      ∧ (∑ i ∈ range 5, bu r t s i = 1)
      ∧ (∑ i ∈ range 5, bu r t s i * cu r t s i = 1/2)
      ∧ (∑ i ∈ range 5, bu r t s i * (∑ j ∈ range 5, Au r t s i j * cu r t s j) = 1/6)
      ∧ (∀ i ∈ range 5, ∀ j ∈ range 5,
          (∑ k ∈ range 5, Ru r t s i k * Au r t s k j)
            + (∑ k ∈ range 5, Ru r t s j k * Au r t s k i)
            - bu r t s i * bu r t s j = 0) := by
  have hv : ∀ i ∈ range 5, vv5 r s i ≠ 0 := fun i hi => (vv5_pos hr hs i hi).ne'
  exact ⟨Au_nonneg hr ht hs, bu_pos hr ht hs, cu_rowsum r t s, cu_mem hr ht hs,
    cu_sorted hr ht hs, Ru_symm r t s, Ru_psd hr2 ht3 hr ht s, Ru_rowsum r t s hr2 ht3,
    m0_u r t s hr2 ht3, m1_u r t s hr2 ht3 hv, m2_u r t s hr2 ht3 hv,
    Mu_zero r t s hr2 ht3 hv⟩

/-- `v` at the endpoint `s = 0`. -/
noncomputable def vL5 : ℕ → ℝ := fun i =>
  match i with
  | 0 => 2/5 | 1 => 1 | 2 => 12/5 | 3 => 21/20 | 4 => 11/20 | _ => 0

/-- `v` at the endpoint `s = -1/50`. -/
noncomputable def vN5 (r : ℝ) : ℕ → ℝ := fun i =>
  match i with
  | 0 => 41/100 + r/100 | 1 => 99/100 - r/100 | 2 => 121/50 | 3 => 21/20 | 4 => 53/100
  | _ => 0

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- `RL = D X D` with `D = diag vL5`. -/
lemma RL_eq_DXD (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∀ i ∈ range 5, ∀ j ∈ range 5, RL r t i j = vL5 i * Xm5 r t i j * vL5 j := by
  intro i hi j hj
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  interval_cases i <;> interval_cases j <;> simp only [RL, Xm5, vL5] <;>
    linear_combination (0:ℝ) * hr + (0:ℝ) * ht3

/-- **`RL` is positive semidefinite.** -/
theorem RL_psd {r t : ℝ} (hr2 : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300))
    (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range 5, ∑ j ∈ range 5, RL r t i j * (x i * x j) := by
  have hrw : ∑ i ∈ range 5, ∑ j ∈ range 5, RL r t i j * (x i * x j)
      = ∑ i ∈ range 5, ∑ j ∈ range 5,
          Xm5 r t i j * ((vL5 i * x i) * (vL5 j * x j)) := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [RL_eq_DXD r t hr2 ht3 i hi j hj]; ring
  rw [hrw]
  exact Xm5_psd hr2 ht3 hr ht (fun i => vL5 i * x i)


/-- **Ten of the eleven conditions of the Claim, at `x = 2/5`.**

For any `r`, `t` in the two rational brackets with `r² = 5` and the cubic reduction, the
five-stage tableau at the left endpoint satisfies: `A ≥ 0` (via `G ≥ 0` and `v > 0`, recorded
here as positivity of the circulant bands), `b > 0`, `c` strictly ordered by `perm5` inside
`(0,1)`, `R` symmetric with `R e = b`, `M = 0`, and the order conditions `bᵀe = 1`,
`bᵀc = 1/2`, `bᵀAc = 1/6`.

The two conditions *not* included are `bᵀc² = 1/3` — which fails at this endpoint by design,
the defect being `dL > 0`, and which is what the sign change of
`tableau_defect_sign_change` supplies at an interior point — and positive semidefiniteness of
`R`, which is included via `RL_psd`. -/
theorem five_conditions_L {r t : ℝ}
    (hr2 : r^2 = 5)
    (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000))
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (0 < g0 r t ∧ 0 < g1 r t ∧ 0 < g2 r t)
      ∧ (∀ i ∈ range 5, 0 < bL r t i)
      ∧ (∀ i ∈ range 5, 0 < cL r t i ∧ cL r t i < 1)
      ∧ (∀ i ∈ range 5, ∀ j ∈ range 5, i < j → cL r t (perm5 i) < cL r t (perm5 j))
      ∧ (∀ i ∈ range 5, ∀ j ∈ range 5, RL r t i j = RL r t j i)
      ∧ (∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 5, ∑ j ∈ range 5, RL r t i j * (x i * x j))
      ∧ (∀ i ∈ range 5, ∑ j ∈ range 5, RL r t i j = bL r t i)
      ∧ (∑ i ∈ range 5, bL r t i = 1)
      ∧ (∑ i ∈ range 5, bL r t i * cL r t i = 1/2)
      ∧ (∑ i ∈ range 5, bL r t i * (∑ j ∈ range 5, AL r t i j * cL r t j) = 1/6)
      ∧ (∀ i ∈ range 5, ∀ j ∈ range 5,
          (∑ k ∈ range 5, RL r t i k * AL r t k j)
            + (∑ k ∈ range 5, RL r t j k * AL r t k i) - bL r t i * bL r t j = 0) :=
  ⟨g_pos hr ht, bL_pos hr ht, cL_mem hr ht, cL_sorted hr ht, RL_symm r t,
   RL_psd hr2 ht3 hr ht, RL_rowsum r t hr2 ht3, m0_L r t, m1_L r t hr2 ht3,
   m2_L r t hr2 ht3, ML_zero r t hr2 ht3⟩

/-! ## A second endpoint on a null direction, and the sign change with `z` constant

The line used above moves `z = Bᵗv`, so the certificate is not constant along it.  That is
avoidable: `ker Bᵗ` is two-dimensional at five stages as well (there is no *rational* vector
in it — the conditions force `d = 0` over `ℚ` — but there are vectors over `ℚ(√5)`).  Taking

  `d = (−φ, φ, −1, 0, 1)`,   `φ = (1+√5)/2`,

which satisfies `Bᵗd = 0`, and moving from `v(0) = (2/5, 1, 12/5, 21/20, 11/20)` to
`v(−1/50) = v(0) − d/50`, the vector `z` — and hence `S`, `h`, `X` — is *constant*.  So along
this segment `bᵀe = 1`, `bᵀc = 1/2` and `bᵀAc = 1/6` hold identically, exactly as in the
six-stage family, and only the order-three defect moves: it is `+9.45×10⁻⁴` at `s = 0` and
`−3.98×10⁻³` at `s = −1/50`.

The endpoint `s = 0` is the tableau `AL`, `bL`, `cL`, `RL` already treated; this section adds
the endpoint `s = −1/50`. -/

/-! ### The tableau at the second endpoint `s = -1/50` of the null-direction line -/

/-- `b` at `s = -1/50`. -/
noncomputable def bN (r t : ℝ) : ℕ → ℝ := fun i =>
  match i with
  | 0 => (((17547991/10960785 : ℝ) + (-4605647/7307190 : ℝ)*r) + ((-147039305/4384314 : ℝ) + (325495003/21921570 : ℝ)*r)*t + ((167561036/730719 : ℝ) + (-24901916/243573 : ℝ)*r)*t^2)
  | 1 => (((145682327/21921570 : ℝ) + (-30715846/10960785 : ℝ)*r) + ((-21405037/162382 : ℝ) + (258293125/4384314 : ℝ)*r)*t + ((503042900/730719 : ℝ) + (-224671148/730719 : ℝ)*r)*t^2)
  | 2 => (((-6229879/362340 : ℝ) + (567103/72468 : ℝ)*r) + ((6761285/18117 : ℝ) + (-1675922/10065 : ℝ)*r)*t + ((-12751832/6039 : ℝ) + (5699536/6039 : ℝ)*r)*t^2)
  | 3 => (((75255215/5845752 : ℝ) + (-33620251/5845752 : ℝ)*r) + ((-401666615/1461438 : ℝ) + (9977576/81191 : ℝ)*r)*t + ((396263980/243573 : ℝ) + (-177294320/243573 : ℝ)*r)*t^2)
  | 4 => (((-256624463/87686280 : ℝ) + (119103667/87686280 : ℝ)*r) + ((293744179/4384314 : ℝ) + (-36708224/1217865 : ℝ)*r)*t + ((-316424204/730719 : ℝ) + (141616000/730719 : ℝ)*r)*t^2)
  | _ => 0

/-- `c` at `s = -1/50`. -/
noncomputable def cN (r t : ℝ) : ℕ → ℝ := fun i =>
  match i with
  | 0 => (((-1191/1676 : ℝ) + (1051/1676 : ℝ)*r) + ((12595/838 : ℝ) + (-4395/838 : ℝ)*r)*t)
  | 1 => (((-5687/9796 : ℝ) + (5929/9796 : ℝ)*r) + ((89645/9796 : ℝ) + (-47085/9796 : ℝ)*r)*t)
  | 2 => (((-105/968 : ℝ) + (105/968 : ℝ)*r) + ((305/121 : ℝ) + (-105/121 : ℝ)*r)*t)
  | 3 => (((-53/420 : ℝ) + (53/420 : ℝ)*r) + ((61/21 : ℝ) + (-1 : ℝ)*r)*t)
  | 4 => (((-9/53 : ℝ) + (10/53 : ℝ)*r) + ((5 : ℝ) + (-80/53 : ℝ)*r)*t)
  | _ => 0

/-- `A` at `s = -1/50`. -/
noncomputable def AN (r t : ℝ) : ℕ → ℕ → ℝ := fun i j =>
  match i, j with
  | 0, 0 => ((1 : ℝ)*t)
  | 0, 1 => (((-1191/1676 : ℝ) + (1051/1676 : ℝ)*r) + ((3398/419 : ℝ) + (-2137/419 : ℝ)*r)*t)
  | 0, 2 => (((4961/838 : ℝ) + (-121/838 : ℝ)*r)*t)
  | 1, 1 => ((1 : ℝ)*t)
  | 1, 2 => (((-5687/9796 : ℝ) + (5929/9796 : ℝ)*r) + ((34727/4898 : ℝ) + (-23595/4898 : ℝ)*r)*t)
  | 1, 3 => (((10395/9796 : ℝ) + (105/9796 : ℝ)*r)*t)
  | 2, 2 => ((1 : ℝ)*t)
  | 2, 3 => (((-105/968 : ℝ) + (105/968 : ℝ)*r) + ((315/242 : ℝ) + (-105/121 : ℝ)*r)*t)
  | 2, 4 => ((53/242 : ℝ)*t)
  | 3, 0 => (((41/105 : ℝ) + (1/105 : ℝ)*r)*t)
  | 3, 3 => ((1 : ℝ)*t)
  | 3, 4 => (((-53/420 : ℝ) + (53/420 : ℝ)*r) + ((53/35 : ℝ) + (-106/105 : ℝ)*r)*t)
  | 4, 0 => (((-9/53 : ℝ) + (10/53 : ℝ)*r) + ((113/53 : ℝ) + (-79/53 : ℝ)*r)*t)
  | 4, 1 => (((99/53 : ℝ) + (-1/53 : ℝ)*r)*t)
  | 4, 4 => ((1 : ℝ)*t)
  | _, _ => 0

/-- `R` at `s = -1/50`. -/
noncomputable def RN (r t : ℝ) : ℕ → ℕ → ℝ := fun i j =>
  match i, j with
  | 0, 0 => (((457698332234119/87373678411800 : ℝ) + (-201106802331089/87373678411800 : ℝ)*r) + ((-2130076427135207/19222209250596 : ℝ) + (4756495344309199/96111046252980 : ℝ)*r)*t + ((588411183806002/889917094935 : ℝ) + (-789234491434942/2669751284805 : ℝ)*r)*t^2)
  | 0, 1 => (((594433375795973/87373678411800 : ℝ) + (-87124057784413/29124559470600 : ℝ)*r) + ((-3991775857157857/32037015417660 : ℝ) + (26727277149909271/480555231264900 : ℝ)*r)*t + ((1725792958972802/2669751284805 : ℝ) + (-771470645511034/2669751284805 : ℝ)*r)*t^2)
  | 0, 2 => (((-674542889611/24069883860 : ℝ) + (45151513025/3610482579 : ℝ)*r) + ((441343950327527/794306167380 : ℝ) + (-328928296606423/1323843612300 : ℝ)*r)*t + ((-13615875133214/4412812041 : ℝ) + (6089449147490/4412812041 : ℝ)*r)*t^2)
  | 0, 3 => (((50260934896207/1941637298040 : ℝ) + (-3374309940197/291245594706 : ℝ)*r) + ((-6775180590187639/12814806167064 : ℝ) + (5050684373069111/21358010278440 : ℝ)*r)*t + ((539728379272789/177983418987 : ℝ) + (-241372570217275/177983418987 : ℝ)*r)*t^2)
  | 0, 4 => (((-241799876591599/29124559470600 : ℝ) + (40879326014636/10921709801475 : ℝ)*r) + ((33627227453234563/192222092505960 : ℝ) + (-25075879402976003/320370154176600 : ℝ)*r)*t + ((-2737147580563753/2669751284805 : ℝ) + (1224232408609591/2669751284805 : ℝ)*r)*t^2)
  | 1, 0 => (((594433375795973/87373678411800 : ℝ) + (-87124057784413/29124559470600 : ℝ)*r) + ((-3991775857157857/32037015417660 : ℝ) + (26727277149909271/480555231264900 : ℝ)*r)*t + ((1725792958972802/2669751284805 : ℝ) + (-771470645511034/2669751284805 : ℝ)*r)*t^2)
  | 1, 1 => (((1724537954527283/87373678411800 : ℝ) + (-762195618611621/87373678411800 : ℝ)*r) + ((-40963315510993231/96111046252980 : ℝ) + (3660188494666255/19222209250596 : ℝ)*r)*t + ((1431288984218462/533950256961 : ℝ) + (-1066534568374234/889917094935 : ℝ)*r)*t^2)
  | 1, 2 => (((-4877063857681/90262064475 : ℝ) + (8736182622581/361048257900 : ℝ)*r) + ((886916603907749/794306167380 : ℝ) + (-1982762376188947/3971530836900 : ℝ)*r)*t + ((-49720361611798/7354686735 : ℝ) + (66709946709182/22064060205 : ℝ)*r)*t^2)
  | 1, 3 => (((13196773071937/291245594706 : ℝ) + (-118236724916653/5824911894120 : ℝ)*r) + ((-11654542471790533/12814806167064 : ℝ) + (26070609877976867/64074030835320 : ℝ)*r)*t + ((313329718259509/59327806329 : ℝ) + (-420405633324425/177983418987 : ℝ)*r)*t^2)
  | 1, 4 => (((-122044194956521/10921709801475 : ℝ) + (438111718977973/87373678411800 : ℝ)*r) + ((40723076180919481/192222092505960 : ℝ) + (-91072723962996623/961110462529800 : ℝ)*r)*t + ((-1031889637478281/889917094935 : ℝ) + (1384397915712029/2669751284805 : ℝ)*r)*t^2)
  | 2, 0 => (((-674542889611/24069883860 : ℝ) + (45151513025/3610482579 : ℝ)*r) + ((441343950327527/794306167380 : ℝ) + (-328928296606423/1323843612300 : ℝ)*r)*t + ((-13615875133214/4412812041 : ℝ) + (6089449147490/4412812041 : ℝ)*r)*t^2)
  | 2, 1 => (((-4877063857681/90262064475 : ℝ) + (8736182622581/361048257900 : ℝ)*r) + ((886916603907749/794306167380 : ℝ) + (-1982762376188947/3971530836900 : ℝ)*r)*t + ((-49720361611798/7354686735 : ℝ) + (66709946709182/22064060205 : ℝ)*r)*t^2)
  | 2, 2 => (((1062114627517/5967739800 : ℝ) + (-94788798257/1193547960 : ℝ)*r) + ((-11776054256689/3282256890 : ℝ) + (13167956097764/8205642225 : ℝ)*r)*t + ((3836682894956/182347605 : ℝ) + (-571958218184/60782535 : ℝ)*r)*t^2)
  | 2, 3 => (((-15227470834709/96279535440 : ℝ) + (6809906904941/96279535440 : ℝ)*r) + ((168542909785565/52953744492 : ℝ) + (-94216762909493/66192180615 : ℝ)*r)*t + ((-26968347033026/1470937347 : ℝ) + (4020040297028/490312449 : ℝ)*r)*t^2)
  | 2, 4 => (((65055239835617/1444193031600 : ℝ) + (-29157867827369/1444193031600 : ℝ)*r) + ((-710163106065113/794306167380 : ℝ) + (15879631433843/39715308369 : ℝ)*r)*t + ((110937006071138/22064060205 : ℝ) + (-3307625092012/1470937347 : ℝ)*r)*t^2)
  | 3, 0 => (((50260934896207/1941637298040 : ℝ) + (-3374309940197/291245594706 : ℝ)*r) + ((-6775180590187639/12814806167064 : ℝ) + (5050684373069111/21358010278440 : ℝ)*r)*t + ((539728379272789/177983418987 : ℝ) + (-241372570217275/177983418987 : ℝ)*r)*t^2)
  | 3, 1 => (((13196773071937/291245594706 : ℝ) + (-118236724916653/5824911894120 : ℝ)*r) + ((-11654542471790533/12814806167064 : ℝ) + (26070609877976867/64074030835320 : ℝ)*r)*t + ((313329718259509/59327806329 : ℝ) + (-420405633324425/177983418987 : ℝ)*r)*t^2)
  | 3, 2 => (((-15227470834709/96279535440 : ℝ) + (6809906904941/96279535440 : ℝ)*r) + ((168542909785565/52953744492 : ℝ) + (-94216762909493/66192180615 : ℝ)*r)*t + ((-26968347033026/1470937347 : ℝ) + (4020040297028/490312449 : ℝ)*r)*t^2)
  | 3, 3 => (((220055326578829/1553309838432 : ℝ) + (-98352838359013/1553309838432 : ℝ)*r) + ((-12255107024353445/4271602055688 : ℝ) + (684986494855607/533950256961 : ℝ)*r)*t + ((979853255687635/59327806329 : ℝ) + (-146066384066890/19775935443 : ℝ)*r)*t^2)
  | 3, 4 => (((-974707300558201/23299647576480 : ℝ) + (87237044010221/4659929515296 : ℝ)*r) + ((10885594839977557/12814806167064 : ℝ) + (-3043143397219037/8009253854415 : ℝ)*r)*t + ((-866549690916455/177983418987 : ℝ) + (129182901368822/59327806329 : ℝ)*r)*t^2)
  | 4, 0 => (((-241799876591599/29124559470600 : ℝ) + (40879326014636/10921709801475 : ℝ)*r) + ((33627227453234563/192222092505960 : ℝ) + (-25075879402976003/320370154176600 : ℝ)*r)*t + ((-2737147580563753/2669751284805 : ℝ) + (1224232408609591/2669751284805 : ℝ)*r)*t^2)
  | 4, 1 => (((-122044194956521/10921709801475 : ℝ) + (438111718977973/87373678411800 : ℝ)*r) + ((40723076180919481/192222092505960 : ℝ) + (-91072723962996623/961110462529800 : ℝ)*r)*t + ((-1031889637478281/889917094935 : ℝ) + (1384397915712029/2669751284805 : ℝ)*r)*t^2)
  | 4, 2 => (((65055239835617/1444193031600 : ℝ) + (-29157867827369/1444193031600 : ℝ)*r) + ((-710163106065113/794306167380 : ℝ) + (15879631433843/39715308369 : ℝ)*r)*t + ((110937006071138/22064060205 : ℝ) + (-3307625092012/1470937347 : ℝ)*r)*t^2)
  | 4, 3 => (((-974707300558201/23299647576480 : ℝ) + (87237044010221/4659929515296 : ℝ)*r) + ((10885594839977557/12814806167064 : ℝ) + (-3043143397219037/8009253854415 : ℝ)*r)*t + ((-866549690916455/177983418987 : ℝ) + (129182901368822/59327806329 : ℝ)*r)*t^2)
  | 4, 4 => (((4661415838703941/349494713647200 : ℝ) + (-2072443345214941/349494713647200 : ℝ)*r) + ((-52896087401977993/192222092505960 : ℝ) + (14777652583438499/120138807816225 : ℝ)*r)*t + ((4251598232524343/2669751284805 : ℝ) + (-126740922293122/177983418987 : ℝ)*r)*t^2)
  | _, _ => 0

/-- The order-three defect at `s = -1/50`. -/
noncomputable def dN (r t : ℝ) : ℝ := (((1077358464234092107/4767562503396221760 : ℝ) + (-1835364117153524437/23837812516981108800 : ℝ)*r) + ((-28910928141953410781/2019592449355343940 : ℝ) + (685521536583271496219/121175546961320636400 : ℝ)*r)*t + ((2749459187107995431393/24235109392264127280 : ℝ) + (-174772332699631071373/3462158484609161040 : ℝ)*r)*t^2)

/-- `bᵀe = 1` at `s = -1/50`. -/
lemma m0_N (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∑ i ∈ range 5, bN r t i = 1 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bN]
  linear_combination (0:ℝ) * hr + (0:ℝ) * ht3

/-- `bᵀc = 1/2` at `s = -1/50`. -/
lemma m1_N (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∑ i ∈ range 5, bN r t i * cN r t i = 1/2 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bN, cN]
  linear_combination ((-4368523242117791/179955220365360 : ℝ) + (21814218239610823/29992536727560 : ℝ)*t + (-7042058289402463/5998507345512 : ℝ)*t^2 + (1222501308927355/749813418189 : ℝ)*t^3) * hr + ((166500/11 : ℝ) + (-74460/11 : ℝ)*r) * ht3

/-- `bᵀAc = 1/6` at `s = -1/50`. -/
lemma m2_N (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∑ i ∈ range 5, bN r t i * (∑ j ∈ range 5, AN r t i j * cN r t j) = 1/6 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bN, cN, AN]
  linear_combination ((3971380681045867/287928352584576 : ℝ) + (-144991568172680983/239940293820480 : ℝ)*t + (469252077256484581/71982088146144 : ℝ)*t^2 + (-209299226031096895/17995522036536 : ℝ)*t^3 + (12803484574457015/749813418189 : ℝ)*t^4 + (-420817663975711/1439641762922880 : ℝ)*r + (8056936908670357/719820881461440 : ℝ)*r*t + (-58499520128746093/359910440730720 : ℝ)*r*t^2 + (786495532834454/749813418189 : ℝ)*r*t^3 + (-1891229195701640/749813418189 : ℝ)*r*t^4) * hr + ((-91825/11 : ℝ) + (1292700/11 : ℝ)*t + (41065/11 : ℝ)*r + (-578100/11 : ℝ)*r*t) * ht3

/-- **`dN` is the order-three defect of the tableau at `s = -1/50`.** -/
lemma defect_N_eq (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ i ∈ range 5, bN r t i * (cN r t i)^2) - 1/3 = dN r t := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bN, cN, dN]
  linear_combination ((110080201528928875845946770589/1989471762863470495196294400 : ℝ) + (-1155703137206412929646985525937/497367940715867623799073600 : ℝ)*t + (76537110141140036297242682441/3315786271439117491993824 : ℝ)*t^2 + (-4461526590852241743902764825/106960847465777983612704 : ℝ)*t^3 + (1215840263654952057846422195/19736823044280461261868 : ℝ)*t^4 + (-2438240180562972650138488867/1989471762863470495196294400 : ℝ)*r + (181579534952903200391515081/3947364608856092252373600 : ℝ)*r*t + (-5373280464206041233440518327/8289465678597793729984560 : ℝ)*r*t^2 + (2295051372681700981760233/565930409871841183136 : ℝ)*r*t^3 + (-187324629195515060699423395/19736823044280461261868 : ℝ)*r*t^4) * hr + ((-81157786491233556606209/2423510939226412728 : ℝ) + (5870514552399223969135/14425660352538171 : ℝ)*t + (576170071276992780295/38468427606768456 : ℝ)*r + (-18377160761680691922845/100979622467767197 : ℝ)*r*t) * ht3

/-- `R e = b` at `s = -1/50`. -/
lemma RN_rowsum (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∀ i ∈ range 5, ∑ j ∈ range 5, RN r t i j = bN r t i := by
  intro i hi
  have hi' := mem_range.1 hi
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  interval_cases i <;> simp only [RN, bN]
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3

/-- `R` is symmetric at `s = -1/50`. -/
lemma RN_symm (r t : ℝ) : ∀ i ∈ range 5, ∀ j ∈ range 5, RN r t i j = RN r t j i := by
  intro i hi j hj
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  interval_cases i <;> interval_cases j <;> simp [RN]

/-- Entry `(0,0)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_0_0 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 0 k * AN r t k 0)
      + (∑ k ∈ range 5, RN r t 0 k * AN r t k 0) - bN r t 0 * bN r t 0 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((8051659009629061/800925385441500 : ℝ) + (-5487943105495924/40046269272075 : ℝ)*t + (-418666406177622359/96111046252980 : ℝ)*t^2 + (3380931932106400/533950256961 : ℝ)*t^3 + (-620105420471056/59327806329 : ℝ)*t^4) * hr + ((-159201579263084/26259848703 : ℝ) + (-55981444706590816/533950256961 : ℝ)*t + (355996081223308/131299243515 : ℝ)*r + (8345181686689952/177983418987 : ℝ)*r*t) * ht3

/-- Entry `(0,1)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_0_1 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 0 k * AN r t k 1)
      + (∑ k ∈ range 5, RN r t 1 k * AN r t k 0) - bN r t 0 * bN r t 1 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((-342791655049775948597/8054105675999724000 : ℝ) + (95277175778226406621/53694037839998160 : ℝ)*t + (-2261319426333934538797/134235094599995400 : ℝ)*t^2 + (17034854250626988769/671175472999977 : ℝ)*t^3 + (-5594742055119568/177983418987 : ℝ)*t^4) * hr + ((78874079828320/2917760967 : ℝ) + (-168211520303237920/533950256961 : ℝ)*t + (-1587311016651856/131299243515 : ℝ)*r + (75226326438778528/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(0,2)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_0_2 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 0 k * AN r t k 2)
      + (∑ k ∈ range 5, RN r t 2 k * AN r t k 0) - bN r t 0 * bN r t 2 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((7964203963670178031/389051160782724000 : ℝ) + (-352745820634327525337/164659026634304400 : ℝ)*t + (37695139460195649001753/815062181839806780 : ℝ)*t^2 + (-4713923647616811897508/67921848486650565 : ℝ)*t^3 + (141929366710976/1470937347 : ℝ)*t^4) * hr + ((-3080387202260/217023543 : ℝ) + (4265650681482592/4412812041 : ℝ)*t + (255103981964/40189545 : ℝ)*r + (-1907655304809632/4412812041 : ℝ)*r*t) * ht3

/-- Entry `(0,3)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_0_3 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 0 k * AN r t k 3)
      + (∑ k ∈ range 5, RN r t 3 k * AN r t k 0) - bN r t 0 * bN r t 3 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((-1845575384580557/320370154176600 : ℝ) + (422530660384865745209/313834603031397360 : ℝ)*t + (-11000118899581035818447/313834603031397360 : ℝ)*t^2 + (136462788089177309851/2615288358594978 : ℝ)*t^3 + (-4414968263917120/59327806329 : ℝ)*t^4) * hr + ((41249328558550/8753282901 : ℝ) + (-132622926977040080/177983418987 : ℝ)*t + (-683196337418/324195663 : ℝ)*r + (59310816967472560/177983418987 : ℝ)*r*t) * ht3

/-- Entry `(0,4)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_0_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 0 k * AN r t k 4)
      + (∑ k ∈ range 5, RN r t 4 k * AN r t k 0) - bN r t 0 * bN r t 4 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((-17075168592909173/961110462529800 : ℝ) + (846273981248530679/3844441850119200 : ℝ)*t + (223388285712707459/26697512848050 : ℝ)*t^2 + (-99148023441380522/8009253854415 : ℝ)*t^3 + (3526509736256000/177983418987 : ℝ)*t^4) * hr + ((282586576526224/26259848703 : ℝ) + (105918013481555344/533950256961 : ℝ)*t + (-1560160829552/324195663 : ℝ)*r + (-47368030519300592/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(1,1)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_1_1 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 1 k * AN r t k 1)
      + (∑ k ∈ range 5, RN r t 1 k * AN r t k 1) - bN r t 1 * bN r t 1 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((-90005770287826119587/447450315333318000 : ℝ) + (3031486947575394763733/402705283799986200 : ℝ)*t + (-2725299278567062307063/50338160474998275 : ℝ)*t^2 + (273466268069784731246/3355877364999885 : ℝ)*t^3 + (-50477124743637904/533950256961 : ℝ)*t^4) * hr + ((3338980096081084/26259848703 : ℝ) + (-168479260986199840/177983418987 : ℝ)*t + (-7466239170123388/131299243515 : ℝ)*r + (226038451672498400/533950256961 : ℝ)*r*t) * ht3

/-- Entry `(1,2)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_1_2 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 1 k * AN r t k 2)
      + (∑ k ∈ range 5, RN r t 2 k * AN r t k 1) - bN r t 1 * bN r t 2 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((71710904110262538388847/163012436367961356000 : ℝ) + (-289861883511640195487603/16301243636796135600 : ℝ)*t + (321325473068409326298697/2037655454599516950 : ℝ)*t^2 + (-16156867731209387849654/67921848486650565 : ℝ)*t^3 + (1280521296187328/4412812041 : ℝ)*t^4) * hr + ((-60478485004880/217023543 : ℝ) + (12817325030529440/4412812041 : ℝ)*t + (135233357151784/1085117715 : ℝ)*r + (-1910693284212512/1470937347 : ℝ)*r*t) * ht3

/-- Entry `(1,3)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_1_3 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 1 k * AN r t k 3)
      + (∑ k ∈ range 5, RN r t 3 k * AN r t k 1) - bN r t 1 * bN r t 3 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((-194807350422958232141/536940378399981600 : ℝ) + (631808548631473313265683/43832232890051831280 : ℝ)*t + (-1075872243506891618825093/8766446578010366256 : ℝ)*t^2 + (202763898459840253387873/1095805822251295782 : ℝ)*t^3 + (-39832918408279360/177983418987 : ℝ)*t^4) * hr + ((2008496541905140/8753282901 : ℝ) + (-398502373706138800/177983418987 : ℝ)*t + (-898224578873608/8753282901 : ℝ)*r + (59405244061325680/59327806329 : ℝ)*r*t) * ht3

/-- Entry `(1,4)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_1_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 1 k * AN r t k 4)
      + (∑ k ∈ range 5, RN r t 4 k * AN r t k 1) - bN r t 1 * bN r t 4 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((21679996880561635469/322164227039988960 : ℝ) + (-4768566122928397957049/1610821135199944800 : ℝ)*t + (12596320007418514482583/402705283799986200 : ℝ)*t^2 + (-262268147347582909/5546904735537 : ℝ)*t^3 + (31817029295168000/533950256961 : ℝ)*t^4) * hr + ((-1122152815023134/26259848703 : ℝ) + (318260095686191600/533950256961 : ℝ)*t + (501847600474274/26259848703 : ℝ)*r + (-47443437498022064/177983418987 : ℝ)*r*t) * ht3

/-- Entry `(2,2)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_2_2 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 2 k * AN r t k 2)
      + (∑ k ∈ range 5, RN r t 2 k * AN r t k 2) - bN r t 2 * bN r t 2 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((-124547162489388943/178627713858000 : ℝ) + (2358273943307966621321/67360510895851800 : ℝ)*t + (-1270000791954079040941/2806687953993825 : ℝ)*t^2 + (42621031917185320088/62370843422085 : ℝ)*t^3 + (-32484710615296/36469521 : ℝ)*t^4) * hr + ((800461898912/1793583 : ℝ) + (-108344257477568/12156507 : ℝ)*t + (-1789892340392/8967915 : ℝ)*r + (145359051099904/36469521 : ℝ)*r*t) * ht3

/-- Entry `(2,3)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_2_3 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 2 k * AN r t k 3)
      + (∑ k ∈ range 5, RN r t 3 k * AN r t k 2) - bN r t 2 * bN r t 3 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((27291186061445400031/51873488104363200 : ℝ) + (-11576882845764300942395/434699830314563616 : ℝ)*t + (126079955795888108207879/362249858595469680 : ℝ)*t^2 + (-1583796803704526654537/3018748821628914 : ℝ)*t^3 + (1010495359435520/1470937347 : ℝ)*t^4) * hr + ((-24361168091680/72341181 : ℝ) + (3368522832596320/490312449 : ℝ)*t + (10894668336524/72341181 : ℝ)*r + (-4519348202707520/1470937347 : ℝ)*r*t) * ht3

/-- Entry `(2,4)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_2_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 2 k * AN r t k 4)
      + (∑ k ∈ range 5, RN r t 4 k * AN r t k 2) - bN r t 2 * bN r t 4 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((-866505844579311979/31124092862617920 : ℝ) + (121624216636536988803881/32602487273592271200 : ℝ)*t + (-355495598361500595483437/4075310909199033900 : ℝ)*t^2 + (596210322478488439930/4528123232443371 : ℝ)*t^3 + (-807145490176000/4412812041 : ℝ)*t^4) * hr + ((4246936637138/217023543 : ℝ) + (-2690238580340576/1470937347 : ℝ)*t + (-1899258933130/217023543 : ℝ)*r + (3609334582481344/4412812041 : ℝ)*r*t) * ht3

/-- Entry `(3,3)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_3_3 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 3 k * AN r t k 3)
      + (∑ k ∈ range 5, RN r t 3 k * AN r t k 3) - bN r t 3 * bN r t 3 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((-4171593321869183/10679005139220 : ℝ) + (15547007337855246379/774900254398512 : ℝ)*t + (-621257004350451581875/2324700763195536 : ℝ)*t^2 + (116658914853191063605/290587595399442 : ℝ)*t^3 + (-31433275904262400/59327806329 : ℝ)*t^4) * hr + ((729880381970600/2917760967 : ℝ) + (-104730507122250800/19775935443 : ℝ)*t + (-326412402263290/2917760967 : ℝ)*r + (140510705749187200/59327806329 : ℝ)*r*t) * ht3

/-- Entry `(3,4)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_3_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 3 k * AN r t k 4)
      + (∑ k ∈ range 5, RN r t 4 k * AN r t k 3) - bN r t 3 * bN r t 4 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((363484341377437/128148061670640 : ℝ) + (-23782594368187588283/10289659115783520 : ℝ)*t + (41547891215248943501543/627669206062794720 : ℝ)*t^2 + (-5251307593290934357/52834108254444 : ℝ)*t^3 + (25107712421120000/177983418987 : ℝ)*t^4) * hr + ((-500996261185/143496441 : ℝ) + (83642025516990640/59327806329 : ℝ)*t + (224058829505/143496441 : ℝ)*r + (-112217533871401280/177983418987 : ℝ)*r*t) * ht3

/-- Entry `(4,4)` of `M` vanishes at `s = -1/50`. -/
lemma Mzero_N_4_4 (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (∑ k ∈ range 5, RN r t 4 k * AN r t k 4)
      + (∑ k ∈ range 5, RN r t 4 k * AN r t k 4) - bN r t 4 * bN r t 4 = 0 := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    RN, AN, bN]
  linear_combination ((29465594745859783/961110462529800 : ℝ) + (-312999659039125373/961110462529800 : ℝ)*t + (-1930578805198435589/120138807816225 : ℝ)*t^2 + (64264371849200744/2669751284805 : ℝ)*t^3 + (-20055091456000000/533950256961 : ℝ)*t^4) * hr + ((-489322487119198/26259848703 : ℝ) + (-66799911385677872/177983418987 : ℝ)*t + (218834471154608/26259848703 : ℝ)*r + (89621460147328000/533950256961 : ℝ)*r*t) * ht3

set_option maxHeartbeats 2000000 in
/-- `b > 0` at `s = -1/50`. -/
lemma bN_pos {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) :
    ∀ i ∈ range 5, 0 < bN r t i := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  intro i hi
  have hi' := mem_range.1 hi
  interval_cases i <;> simp only [bN] <;> nlinarith [hr1, hr2, ht1, ht2]

/-- The abscissas at `s = -1/50` lie strictly inside `(0,1)`. -/
lemma cN_mem {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) :
    ∀ i ∈ range 5, 0 < cN r t i ∧ cN r t i < 1 := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  intro i hi
  have hi' := mem_range.1 hi
  interval_cases i <;> simp only [cN] <;> constructor <;> nlinarith [hr1, hr2, ht1, ht2]

/-- The abscissas at `s = -1/50` are strictly ordered by `perm5`. -/
lemma cN_sorted {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) :
    ∀ i ∈ range 5, ∀ j ∈ range 5, i < j → cN r t (perm5 i) < cN r t (perm5 j) := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  intro i hi j hj hij
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  interval_cases i <;> interval_cases j <;> simp only [perm5, cN] <;>
    first
      | exact absurd hij (by omega)
      | nlinarith [hr1, hr2, ht1, ht2]

/-- The defect at `s = -1/50` is negative on the brackets. -/
lemma dN_neg {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000)) : dN r t < 0 := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨ht1, ht2⟩ := ht
  unfold dN
  nlinarith [hr1, hr2, ht1, ht2, mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hr1),
    sq_nonneg t, sq_nonneg (t - 35127/1000000), sq_nonneg (r - 2236067/1000000)]

/-- **`M = 0` at `s = -1/50`**, from the fifteen entry lemmas. -/
lemma MN_zero (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∀ i ∈ range 5, ∀ j ∈ range 5,
      (∑ k ∈ range 5, RN r t i k * AN r t k j)
        + (∑ k ∈ range 5, RN r t j k * AN r t k i) - bN r t i * bN r t j = 0 := by
  intro i hi j hj
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  interval_cases i <;> interval_cases j
  case _ => exact Mzero_N_0_0 r t hr ht3
  case _ => exact Mzero_N_0_1 r t hr ht3
  case _ => exact Mzero_N_0_2 r t hr ht3
  case _ => exact Mzero_N_0_3 r t hr ht3
  case _ => exact Mzero_N_0_4 r t hr ht3
  case _ => linear_combination Mzero_N_0_1 r t hr ht3
  case _ => exact Mzero_N_1_1 r t hr ht3
  case _ => exact Mzero_N_1_2 r t hr ht3
  case _ => exact Mzero_N_1_3 r t hr ht3
  case _ => exact Mzero_N_1_4 r t hr ht3
  case _ => linear_combination Mzero_N_0_2 r t hr ht3
  case _ => linear_combination Mzero_N_1_2 r t hr ht3
  case _ => exact Mzero_N_2_2 r t hr ht3
  case _ => exact Mzero_N_2_3 r t hr ht3
  case _ => exact Mzero_N_2_4 r t hr ht3
  case _ => linear_combination Mzero_N_0_3 r t hr ht3
  case _ => linear_combination Mzero_N_1_3 r t hr ht3
  case _ => linear_combination Mzero_N_2_3 r t hr ht3
  case _ => exact Mzero_N_3_3 r t hr ht3
  case _ => exact Mzero_N_3_4 r t hr ht3
  case _ => linear_combination Mzero_N_0_4 r t hr ht3
  case _ => linear_combination Mzero_N_1_4 r t hr ht3
  case _ => linear_combination Mzero_N_2_4 r t hr ht3
  case _ => linear_combination Mzero_N_3_4 r t hr ht3
  case _ => exact Mzero_N_4_4 r t hr ht3


/-- **Ten of the eleven conditions at `s = −1/50`.** -/
theorem five_conditions_N {r t : ℝ}
    (hr2 : r^2 = 5)
    (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000))
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    (0 < g0 r t ∧ 0 < g1 r t ∧ 0 < g2 r t)
      ∧ (∀ i ∈ range 5, 0 < bN r t i)
      ∧ (∀ i ∈ range 5, 0 < cN r t i ∧ cN r t i < 1)
      ∧ (∀ i ∈ range 5, ∀ j ∈ range 5, i < j → cN r t (perm5 i) < cN r t (perm5 j))
      ∧ (∀ i ∈ range 5, ∀ j ∈ range 5, RN r t i j = RN r t j i)
      ∧ (∀ i ∈ range 5, ∑ j ∈ range 5, RN r t i j = bN r t i)
      ∧ (∑ i ∈ range 5, bN r t i = 1)
      ∧ (∑ i ∈ range 5, bN r t i * cN r t i = 1/2)
      ∧ (∑ i ∈ range 5, bN r t i * (∑ j ∈ range 5, AN r t i j * cN r t j) = 1/6)
      ∧ (∀ i ∈ range 5, ∀ j ∈ range 5,
          (∑ k ∈ range 5, RN r t i k * AN r t k j)
            + (∑ k ∈ range 5, RN r t j k * AN r t k i) - bN r t i * bN r t j = 0) :=
  ⟨g_pos hr ht, bN_pos hr ht, cN_mem hr ht, cN_sorted hr ht, RN_symm r t,
   RN_rowsum r t hr2 ht3, m0_N r t hr2 ht3, m1_N r t hr2 ht3, m2_N r t hr2 ht3,
   MN_zero r t hr2 ht3⟩

/-- **The defect changes sign between the two endpoints of the null-direction segment**,
with the ten other conditions holding at *both* ends.  Along this segment `z = Bᵗv` is
constant, so `bᵀe = 1`, `bᵀc = 1/2` and `bᵀAc = 1/6` hold identically. -/
theorem five_sign_change_uniform :
    ∃ t : ℝ, t ∈ Set.Ioo (35127/1000000 : ℝ) (35128/1000000)
      ∧ ((∑ i ∈ range 5, bN (Real.sqrt 5) t i * (cN (Real.sqrt 5) t i)^2) - 1/3 < 0)
      ∧ (0 < (∑ i ∈ range 5, bL (Real.sqrt 5) t i * (cL (Real.sqrt 5) t i)^2) - 1/3) := by
  obtain ⟨t, htmem, hcub⟩ := tau5_cubic
  have hr2 : (Real.sqrt 5)^2 = 5 := sqrt5_sq
  have ht3 := cubic_reduce (Real.sqrt 5) t hr2 hcub
  have hIcc : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000) :=
    Set.mem_Icc.2 ⟨le_of_lt htmem.1, le_of_lt htmem.2⟩
  refine ⟨t, htmem, ?_, ?_⟩
  · rw [defect_N_eq (Real.sqrt 5) t hr2 ht3]
    exact dN_neg sqrt5_bracket hIcc
  · rw [defect_L_eq (Real.sqrt 5) t hr2 ht3]
    exact dL_pos sqrt5_bracket hIcc

/-! ## The refutation at five stages

`five_uniform` gives the ten structural conditions at every `s`; the defect of the *uniform*
family agrees with `dL` at `s = 0` and with `dN` at `s = −1/50`, whose signs are opposite, so
the intermediate value theorem supplies an `s` where `bᵀc² = 1/3` as well. -/

/-- The order-three defect of the uniform family. -/
noncomputable def defu (r t s : ℝ) : ℝ :=
  (∑ i ∈ range 5, bu r t s i * (cu r t s i)^2) - 1/3

/-- `vv5` is continuous in `s`. -/
lemma vv5_cont (r : ℝ) (i : ℕ) : Continuous (fun s => vv5 r s i) := by
  match i with
  | 0 => simp only [vv5]; fun_prop
  | 1 => simp only [vv5]; fun_prop
  | 2 => simp only [vv5]; fun_prop
  | 3 => simp only [vv5]; fun_prop
  | 4 => simp only [vv5]; fun_prop
  | (n+5) => simp only [vv5]; fun_prop

/-- The defect is continuous on the segment. -/
lemma defu_cont {r t : ℝ} (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000)) :
    ContinuousOn (defu r t) (Set.Icc (-1/50 : ℝ) 0) := by
  unfold defu cu bu
  apply ContinuousOn.sub _ continuousOn_const
  apply continuousOn_finsetSum
  intro i hi
  apply ContinuousOn.mul
  · exact ((vv5_cont r i).continuousOn).mul continuousOn_const
  · apply ContinuousOn.pow
    apply ContinuousOn.div
    · apply continuousOn_finsetSum
      intro j _
      exact continuousOn_const.mul ((vv5_cont r j).continuousOn)
    · exact (vv5_cont r i).continuousOn
    · intro s hs
      exact (vv5_pos hr hs i hi).ne'



set_option maxHeartbeats 4000000 in
/-- The uniform weights agree with `bL` at that endpoint. -/
lemma bu_at_L (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∀ i ∈ range 5, bu r t 0 i = bL r t i := by
  intro i hi
  have hi' := mem_range.1 hi
  interval_cases i <;> simp only [bu, bL, vv5, hv5]
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3

set_option maxHeartbeats 4000000 in
/-- The uniform abscissas agree with `cL` at that endpoint. -/
lemma cu_at_L (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300))
    (hv : ∀ i ∈ range 5, vv5 r 0 i ≠ 0) :
    ∀ i ∈ range 5, cu r t 0 i = cL r t i := by
  intro i hi
  have hi' := mem_range.1 hi
  have h0 := hv i hi
  unfold cu
  rw [div_eq_iff h0]
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  interval_cases i <;> simp only [cL, Gm5, vv5] at h0 ⊢
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3

set_option maxHeartbeats 4000000 in
/-- The uniform weights agree with `bN` at that endpoint. -/
lemma bu_at_N (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300)) :
    ∀ i ∈ range 5, bu r t (-1/50) i = bN r t i := by
  intro i hi
  have hi' := mem_range.1 hi
  interval_cases i <;> simp only [bu, bN, vv5, hv5]
  case _ => linear_combination ((-1435777/87686280 : ℝ) + (466736/1217865 : ℝ)*t + (-1927504/730719 : ℝ)*t^2) * hr + (0:ℝ) * ht3
  case _ => linear_combination ((2423869/87686280 : ℝ) + (-141742/243573 : ℝ)*t + (2219212/730719 : ℝ)*t^2) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3

set_option maxHeartbeats 4000000 in
/-- The uniform abscissas agree with `cN` at that endpoint. -/
lemma cu_at_N (r t : ℝ) (hr : r^2 = 5)
    (ht3 : t^3 = (1/2 + r/10)*t^2 + (-1/4 - r/10)*t + (1/120 + r/300))
    (hv : ∀ i ∈ range 5, vv5 r (-1/50) i ≠ 0) :
    ∀ i ∈ range 5, cu r t (-1/50) i = cN r t i := by
  intro i hi
  have hi' := mem_range.1 hi
  have h0 := hv i hi
  unfold cu
  rw [div_eq_iff h0]
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  interval_cases i <;> simp only [cN, Gm5, vv5] at h0 ⊢
  case _ => linear_combination ((-147/16760 : ℝ) + (6071/83800 : ℝ)*t) * hr + (0:ℝ) * ht3
  case _ => linear_combination ((5929/979600 : ℝ) + (-9417/195920 : ℝ)*t) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination (0:ℝ) * hr + (0:ℝ) * ht3
  case _ => linear_combination ((1/400 : ℝ) + (-1/50 : ℝ)*t) * hr + (0:ℝ) * ht3

/-- **The order-three defect of the five-stage tableau changes sign.** -/
theorem tableau_defect_sign_change :
    ∃ t : ℝ, t ∈ Set.Ioo (35127/1000000 : ℝ) (35128/1000000)
      ∧ quin t = 0
      ∧ 0 < (∑ i ∈ range 5, bL (Real.sqrt 5) t i * (cL (Real.sqrt 5) t i)^2) - 1/3
      ∧ (∑ i ∈ range 5, bR (Real.sqrt 5) t i * (cR (Real.sqrt 5) t i)^2) - 1/3 < 0 := by
  obtain ⟨t, htmem, hcub⟩ := tau5_cubic
  have hr : (Real.sqrt 5)^2 = 5 := sqrt5_sq
  have ht3 := cubic_reduce (Real.sqrt 5) t hr hcub
  have hIcc : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000) :=
    Set.mem_Icc.2 ⟨le_of_lt htmem.1, le_of_lt htmem.2⟩
  refine ⟨t, htmem, cubic_to_minpoly _ t hr hcub, ?_, ?_⟩
  · rw [defect_L_eq (Real.sqrt 5) t hr ht3]
    exact dL_pos sqrt5_bracket hIcc
  · rw [defect_R_eq (Real.sqrt 5) t hr ht3]
    exact dR_neg sqrt5_bracket hIcc

/-- **The defect changes sign** at the five-stage parameter. -/
theorem defect5_sign_change :
    ∃ t : ℝ, quin t = 0 ∧ t ∈ Set.Ioo (35127/1000000 : ℝ) (35128/1000000)
      ∧ 0 < dL (Real.sqrt 5) t ∧ dR (Real.sqrt 5) t < 0 := by
  obtain ⟨t, htmem, h0⟩ := tau5_exists
  have hIcc : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000) :=
    Set.mem_Icc.2 ⟨le_of_lt htmem.1, le_of_lt htmem.2⟩
  exact ⟨t, h0, htmem, dL_pos sqrt5_bracket hIcc, dR_neg sqrt5_bracket hIcc⟩

/-- **The order-three condition is attained** along the line: any continuous interpolation of
the defect between the two endpoint values vanishes strictly inside `(2/5, 21/50)`. -/
theorem five_stage_defect_root (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (2/5 : ℝ) (21/50)))
    {t : ℝ} (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000))
    (hfL : f (2/5) = dL (Real.sqrt 5) t) (hfR : f (21/50) = dR (Real.sqrt 5) t) :
    ∃ x ∈ Set.Ioo (2/5 : ℝ) (21/50), f x = 0 := by
  have hmem : (0:ℝ) ∈ Set.Ioo (f (21/50)) (f (2/5)) := by
    rw [hfL, hfR]
    exact Set.mem_Ioo.2 ⟨dR_neg sqrt5_bracket ht, dL_pos sqrt5_bracket ht⟩
  obtain ⟨x, hx, h0⟩ :=
    intermediate_value_Ioo' (by norm_num : (2/5 : ℝ) ≤ 21/50) hf hmem
  exact ⟨x, hx, h0⟩

/-- **The Claim is false at five stages.**  All eleven conditions hold simultaneously. -/
theorem claim_is_false_five :
    ∃ (r t s : ℝ), r^2 = 5
      ∧ (∀ i ∈ range 5, ∀ j ∈ range 5, 0 ≤ Au r t s i j)
      ∧ (∀ i ∈ range 5, 0 < bu r t s i)
      ∧ (∀ i ∈ range 5, cu r t s i = ∑ j ∈ range 5, Au r t s i j)
      ∧ (∀ i ∈ range 5, 0 < cu r t s i ∧ cu r t s i < 1)
      ∧ (∀ i ∈ range 5, ∀ j ∈ range 5, i < j → cu r t s (perm5 i) < cu r t s (perm5 j))
      ∧ (∀ i ∈ range 5, ∀ j ∈ range 5, Ru r t s i j = Ru r t s j i)
      ∧ (∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 5, ∑ j ∈ range 5, Ru r t s i j * (x i * x j))
      ∧ (∀ i ∈ range 5, ∑ j ∈ range 5, Ru r t s i j = bu r t s i)
      ∧ (∑ i ∈ range 5, bu r t s i = 1)
      ∧ (∑ i ∈ range 5, bu r t s i * cu r t s i = 1/2)
      ∧ (∑ i ∈ range 5, bu r t s i * (∑ j ∈ range 5, Au r t s i j * cu r t s j) = 1/6)
      ∧ (∑ i ∈ range 5, bu r t s i * (cu r t s i)^2 = 1/3)
      ∧ (∀ i ∈ range 5, ∀ j ∈ range 5,
          (∑ k ∈ range 5, Ru r t s i k * Au r t s k j)
            + (∑ k ∈ range 5, Ru r t s j k * Au r t s k i)
            - bu r t s i * bu r t s j = 0) := by
  obtain ⟨t, htmem, hcub⟩ := tau5_cubic
  set r := Real.sqrt 5 with hrdef
  have hr2 : r^2 = 5 := sqrt5_sq
  have ht3 := cubic_reduce r t hr2 hcub
  have hrb := sqrt5_bracket
  have htb : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000) :=
    Set.mem_Icc.2 ⟨le_of_lt htmem.1, le_of_lt htmem.2⟩
  -- the defect at the two ends
  have hvL : ∀ i ∈ range 5, vv5 r 0 i ≠ 0 := fun i hi =>
    (vv5_pos hrb (by norm_num) i hi).ne'
  have hvN : ∀ i ∈ range 5, vv5 r (-1/50) i ≠ 0 := fun i hi =>
    (vv5_pos hrb (by norm_num) i hi).ne'
  have hL : 0 < defu r t 0 := by
    unfold defu
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [bu_at_L r t hr2 ht3 i hi, cu_at_L r t hr2 ht3 hvL i hi])]
    rw [defect_L_eq r t hr2 ht3]
    exact dL_pos hrb htb
  have hN : defu r t (-1/50) < 0 := by
    unfold defu
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [bu_at_N r t hr2 ht3 i hi, cu_at_N r t hr2 ht3 hvN i hi])]
    rw [defect_N_eq r t hr2 ht3]
    exact dN_neg hrb htb
  obtain ⟨s, hs, h0⟩ := intermediate_value_Ioo (by norm_num : (-1/50 : ℝ) ≤ 0)
    (defu_cont hrb) (Set.mem_Ioo.2 ⟨hN, hL⟩)
  have hsIcc : s ∈ Set.Icc (-1/50 : ℝ) 0 :=
    Set.mem_Icc.2 ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  obtain ⟨q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12⟩ := five_uniform hr2 ht3 hrb htb hsIcc
  refine ⟨r, t, s, hr2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, ?_, q12⟩
  unfold defu at h0
  linarith


/-! ## Counterexamples at every stage count `≥ 5`

`SSPLean/SixStageWitness.lean` develops padding by a zero-weight stage for
`WeakAlgStabData` — the Claim's hypotheses with its own `b ≥ 0` — and shows the zero weight
is forced.  That machinery is generic in the stage count, so it applies here: relabelling the
five-stage tableau by `perm5` and packaging it as a `StrictWeak 5` gives witnesses at every
`s ≥ 5`. -/

/-- The inverse of `perm5` on `range 5`. -/
def iperm5 : ℕ → ℕ := fun k =>
  match k with
  | 2 => 0 | 3 => 1 | 4 => 2 | 1 => 3 | 0 => 4 | _ => 5

lemma iperm5_perm5 : ∀ i ∈ range 5, iperm5 (perm5 i) = i := by
  intro i hi
  have := mem_range.1 hi
  interval_cases i <;> rfl

lemma perm5_eq_five {k : ℕ} (hk : ¬ k < 5) : perm5 k = 5 := by
  match k, hk with
  | 0, h => omega
  | 1, h => omega
  | 2, h => omega
  | 3, h => omega
  | 4, h => omega
  | (n+5), _ => rfl

lemma sum_perm5 (f : ℕ → ℝ) : ∑ k ∈ range 5, f (perm5 k) = ∑ i ∈ range 5, f i := by
  simp only [show (5:ℕ)=4+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, perm5]
  ring

lemma sum_perm5_2 (f : ℕ → ℕ → ℝ) :
    ∑ i ∈ range 5, ∑ j ∈ range 5, f (perm5 i) (perm5 j)
      = ∑ i ∈ range 5, ∑ j ∈ range 5, f i j := by
  rw [sum_perm5 (fun i => ∑ j ∈ range 5, f i (perm5 j))]
  exact Finset.sum_congr rfl fun i _ => sum_perm5 (fun j => f i j)

/-- Permuted coefficient matrix. -/
noncomputable def Ap5 (r t s : ℝ) : ℕ → ℕ → ℝ := fun i j => Au r t s (perm5 i) (perm5 j)
/-- Permuted weights. -/
noncomputable def bp5 (r t s : ℝ) : ℕ → ℝ := fun i => bu r t s (perm5 i)
/-- Permuted certificate. -/
noncomputable def Rp5 (r t s : ℝ) : ℕ → ℕ → ℝ := fun i j => Ru r t s (perm5 i) (perm5 j)
/-- Permuted abscissas. -/
noncomputable def cp5 (r t s : ℝ) : ℕ → ℝ := fun i => cu r t s (perm5 i)

/-- `A ≥ 0` globally: off `range 5` the coefficient vanishes since `vv5` does. -/
lemma Ap5_nonneg_all {r t s : ℝ}
    (hr : r ∈ Set.Icc (2236067/1000000 : ℝ) (2236068/1000000))
    (ht : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000))
    (hs : s ∈ Set.Icc (-1/50 : ℝ) 0) : ∀ i j, 0 ≤ Ap5 r t s i j := by
  intro i j
  by_cases hi : i < 5
  · by_cases hj : j < 5
    · exact Au_nonneg hr ht hs _ (perm5_mem i (mem_range.2 hi)) _ (perm5_mem j (mem_range.2 hj))
    · simp [Ap5, Au, perm5_eq_five hj, vv5, Gm5]
  · simp [Ap5, Au, perm5_eq_five hi, vv5, Gm5]

lemma Ap5_rowsum (r t s : ℝ) (i : ℕ) :
    ∑ j ∈ range 5, Ap5 r t s i j = ∑ j ∈ range 5, Au r t s (perm5 i) j :=
  sum_perm5 (fun j => Au r t s (perm5 i) j)

lemma Rp5_rowsum (r t s : ℝ) (i : ℕ) :
    ∑ j ∈ range 5, Rp5 r t s i j = ∑ j ∈ range 5, Ru r t s (perm5 i) j :=
  sum_perm5 (fun j => Ru r t s (perm5 i) j)

lemma Mp5_inner (r t s : ℝ) (i j : ℕ) :
    ∑ k ∈ range 5, Rp5 r t s i k * Ap5 r t s k j
      = ∑ k ∈ range 5, Ru r t s (perm5 i) k * Au r t s k (perm5 j) :=
  sum_perm5 (fun k => Ru r t s (perm5 i) k * Au r t s k (perm5 j))


end Five

end Counterexample

end SSP
