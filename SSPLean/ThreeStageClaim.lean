import Mathlib

/-!
# Towards Theorem 1 of `s3_general_claim_proof.tex`

That note proves the general Claim is **inconsistent at `s = 3`**, with no sign condition on
`R`, no distinctness of the `cᵢ`, no upper bound on `c`, and no strict positivity of `b`.  This
file is a partial formalization: the hypothesis bundle and the first structural lemmas.

## What is proved here

* `Data` — the hypotheses of the Claim at `s = 3`, bundled.  An inhabitant is a
  counterexample; Theorem 1 asserts there is none.
* `not_two_zero` — **Lemma 1**: at most one weight vanishes.
* `psd_kernel` — if a symmetric PSD form vanishes at `x`, then `Mx = 0`.  Proved from
  scratch: `t ↦ (x+tz)ᵗM(x+tz) = 2tB + t²Q ≥ 0` for all `t` forces `B = 0` (take `t = −sB`,
  `s → 0⁺`).
* `psd_cauchy` — Cauchy–Schwarz for a PSD form, `(xᵗRy)² ≤ (xᵗRx)(yᵗRy)`, including the
  degenerate case `yᵗRy = 0` (which `psd_kernel` settles).
* `Rcol` — the column sums of `R` are `b`, by symmetry and `Re = b`.
* `eMe_zero`, `Msymm`, `Me_zero`, `Rc_eq` — **Lemma 3**: `eᵗMe = 2bᵗc − (bᵗe)² = 0`, hence
  `Me = 0`, hence the kernel identity `R c + Aᵀ b = b` coordinatewise.
* `eRx`, `eRe`, `K_psd` — **Lemma 5**: `K = R − b bᵀ ⪰ 0`, from
  `(bᵗx)² = (eᵗRx)² ≤ (eᵗRe)(xᵗRx) = xᵗRx`.
* `cRc` — **Lemma 6** (redundancy): `cᵗRc = 1/3`, equivalent to `bᵗAc = 1/6` given the
  kernel identity.
* `cKc`, `cKc_ne` — **Lemma 8**: `cᵗKc = 1/12 ≠ 0`, so `K` does not vanish on the quotient
  `ℝ³/⟨e⟩`.  This is what makes the note's rank dichotomy nontrivial.

## The accretive factorization and the second-order test

* `Km`, `Bm` — the matrices `K = R − b bᵀ` and `B = A − c bᵀ`.
* `Km_e`, `Bm_e` — **`K e = 0`** and **`B e = 0`**, so both descend to `ℝ³/⟨e⟩`.
* `M_factor` — **Lemma 9**: `M = K B + Bᵀ K` entrywise.  The certificate is
  `M − (KB + BᵀK) = bᵢrⱼ + bⱼrᵢ − 2(bᵀc − 1/2)bᵢbⱼ` where `rₖ` is the kernel identity at `k`;
  it also needs symmetry of `R` to match `Rⱼₖ` with `Rₖⱼ` inside the `BᵀK` sum.
* `cMc` — **Lemma 12**: `cᵀMc = 1/12 − 2 bᵀA²c`.
* `bA2c_le` — hence **`bᵀA²c ≤ 1/24`**, from `cᵀMc ≥ 0`.

## The endgame arithmetic

Stated as self-contained real-number facts.  These are the arithmetic cores of the note's
impossibility propositions; connecting them to `Data` needs the quotient-rank dichotomy.

* `rank_one_recursion`, `rank_one_p5` — **Proposition `rank1`**: with `p₀ = 1/2`, `r₀ = 1`,
  `pₖ₊₁ = ½pₖ − (1/12)rₖ`, `rₖ₊₁ = pₖ + λrₖ`, the fifth iterate is
  `p₅ = −(144λ⁴+144λ³+72λ²+36λ+1)/1728 < 0` for every `λ ≥ 0`.  Since `pₖ = bᵀAᵏc ≥ 0`, that
  is the contradiction.
* `sum_sq_ge`, `pair_sum_le`, `trace_trichotomy` — **Proposition `trich`**: `Σdᵢ² ≥ θ²/3`,
  hence `σ₂ ≤ θ²/3`, hence `θ = 1/2` or `θ ≥ 1`, from
  `θ²/3 − (θ/2 − 1/6) = (2θ−1)(θ−1)/6`.
* `nilpotent_obstruction` — **Lemma `nilpotent`**: for `X = uvᵀ` nilpotent and `K ≻ 0`,
  `Qu = (uᵀKu)v ≠ 0`, so `Q = KX + XᵀK` cannot be positive semidefinite.
* `Bzero_obstruction`, `Bzero_quantity` — **Lemma `Bzero`**: `γ² − γ/2 + 1/12 =
  (γ−1/4)² + 1/48 > 0`, so the degenerate case `B̄ = 0` is impossible.
* `rank_two_key` — **Proposition `rank2`**, the note's hardest inequality: with
  `g = (1/3−c₁)/(1−2c₁)`,
  `g(u−g) − ((c₁+u)/2 − 1/6 − c₁u) = (12c₁²−6c₁+1)(6c₁u−3c₁−3u+1)/(18(2c₁−1)²) < 0`
  for `0 ≤ c₁ ≤ 1/3` and `u > 1−c₁`.

## The trichotomy machinery, and one case closed completely

* `theta`, `sig2A`, `sig2B`, `trB` — the trace `θ = tr A`, the second elementary symmetric
  functions of `A` and `B`, and `tr B = θ − 1/2`.
* `Delta_id` — **Lemma 17**: `σ₂(B) = σ₂(A) − θ/2 + 1/6`.
* `sig2A_le` — `σ₂(A) ≤ θ²/3`, using `A ≥ 0` (so `aᵢⱼaⱼᵢ ≥ 0`) and `pair_sum_le`.
* `trichotomy_input` — given accretivity (`θ ≥ 1/2` and `Δ ≥ 0`), concludes `θ = 1/2` or
  `θ ≥ 1`.
* `c_nonneg`, `diag_le`, `diag_part_le` — **Lemma 18**: `c ≥ 0`, `aᵢᵢ ≤ cᵢ`, and the diagonal
  part of `bᵀAc` is at most `1/6`.
* `pair_sum_eq_imp`, `theta_one_diag` — equality in the pair bound forces `d₁ = d₂ = d₃`, so
  at `θ = 1` the diagonal is `1/3` throughout.
* `theta_one_impossible` — **Proposition `sone`, complete**: `θ = 1` contradicts the
  hypotheses.  Given `Δ ≥ 0`, the diagonal is forced to `1/3`, the diagonal part of `bᵀAc` is
  then exactly `1/6`, so every off-diagonal `bᵢaᵢⱼcⱼ` vanishes; since `cⱼ ≥ 1/3 > 0` this gives
  `bᵢaᵢⱼ = 0`, whence `bᵀc = (1/3)bᵀe = 1/3`, contradicting `bᵀc = 1/2`.

## Accretivity (item 4 of the old gap list)

For a `2 × 2` block, `K ≻ 0` and `Q = K X + Xᵀ K ⪰ 0` force `tr X ≥ 0` and `det X ≥ 0` — the
two facts the trichotomy needs.  Both are proved directly in coordinates, with no eigenvalue
machinery from Mathlib:

* `Qform`, `Qform_eq` — the quadratic form of `Q` in explicit coordinates.
* `det_nonneg_of_accretive` — if `X v = λ v` with `λ < 0` and `vᵀKv > 0`, then
  `vᵀQv = 2λ(vᵀKv) < 0`.
* `eigenvector_of_root` — for a root `λ` of the characteristic polynomial, `v = (x₁₂, λ − x₁₁)`
  satisfies both eigen-equations (the first identically, the second exactly at a root).
* `det_nonneg_accretive_generic` — hence **`det X ≥ 0`** when `x₁₂ ≠ 0`: if `det X < 0` the
  discriminant is positive, the smaller root `λ = (tr − √disc)/2` is negative (from
  `λ(tr − λ) = det < 0`), and its eigenvector contradicts `Q ⪰ 0`.
* `trace_nonneg_accretive` — **`tr X ≥ 0`**, from the identity
  `tr(adj K · Q) = 2 det(K) · tr X` together with the explicit Cholesky factorization
  `adj K = vvᵀ + wwᵀ`, `v = (√k₂₂, −k₁₂/√k₂₂)`, `w = (0, √(det K / k₂₂))`.  So
  `2 det(K) tr X = Q(v) + Q(w) ≥ 0`.

## The quotient `ℝ³/⟨e⟩` and the rank dichotomy

Rather than build an abstract quotient, we fix the explicit complement basis
`f₁ = (1,−1,0)`, `f₂ = (0,1,−1)` (with `e` these span `ℝ³`; the determinant is `3`), so the
quotient form becomes a concrete `2 × 2` matrix `K̄ᵢⱼ = fᵢᵀKfⱼ`.

* `f1`, `f2`, `Kpair`, `kb11`, `kb12`, `kb22`, `Kpair_symm` — the basis and the quotient form.
* `Kb_psd` — **`K̄ ⪰ 0`**, the restriction of `K ⪰ 0`.
* `s1c`, `s2c`, `c_decomp` — the quotient coordinates of `c`: `c = αe + s₁f₁ + s₂f₂` with
  `s₁ = (2c₀−c₁−c₂)/3`, `s₂ = (c₀+c₁−2c₂)/3`.
* `Kb_ne_zero` — **`K̄` does not vanish**: evaluated at `(s₁, s₂)` it equals `cᵀKc = 1/12`,
  the `e`-component being killed by `Ke = 0`.
* `rank_dichotomy` — hence `det K̄ > 0` (rank two) or `det K̄ = 0` (rank one).
* `Kb_pd_of_rank_two` — in the rank-two case `K̄` is positive definite, which is exactly the
  hypothesis the accretivity lemmas need.

## The quotient of `B`, and the discharged hypotheses

* `xb11`, `xb12`, `xb21`, `xb22` — the matrix `B̄` of `B` on the quotient, in the basis
  `(f₁, f₂)`; each entry is a coordinate of `B fⱼ` in the basis `(e, f₁, f₂)`.
* `trace_xb` — `tr B̄ = tr B = θ − 1/2`, and `det_xb` — `det B̄ = σ₂(B) = Δ`.  Both hold because
  `B e = 0` makes the third eigenvalue of `B` zero, so the quotient carries all the spectral
  information the trichotomy uses.
* `Mform_quotient` — the `M`-form descends: at `v = t₁f₁ + t₂f₂` the quadratic form of
  `M = KB + BᵗK` is exactly `Qform (K̄, B̄) (t₁, t₂)`.  Hence `Qform_quotient_psd`.
* `det_nonneg_accretive_diag` — the `x₁₂ = 0` companion to `det_nonneg_accretive_generic`
  (there `(x₁₁ − x₂₂, x₂₁)` is the eigenvector for `λ = x₁₁`).
* `sig2B_nonneg` and `theta_ge_half` — **`Δ ≥ 0` and `θ ≥ 1/2` are now theorems**, in the
  rank-two case, rather than assumptions.  Consequently `trichotomy_rank_two` and
  `theta_one_impossible_rank_two` carry no hypotheses beyond `det K̄ > 0`.

## The rank-one branch — closed

* `psd_det_nonneg` — a psd `2 × 2` form has nonnegative determinant (elementary, by testing at
  `(b,−a)`, `(−c,b)`, or `(1,±1)`).
* `rank_one_normal_form` — a singular psd `2 × 2` form is `w wᵗ`, with
  `w = (√k₁₁, k₁₂/√k₁₁)` or `(0, √k₂₂)`.
* `rank_one_eigen` — if `w uᵗ + u wᵗ ⪰ 0` and `w ≠ 0` then `u = λw` with `λ ≥ 0`.  The clean
  route: `det(w uᵗ + u wᵗ) = −(u₁w₂ − u₂w₁)²`, so semidefiniteness forces `u ∥ w`; then
  testing at `w` gives `2λ|w|⁴ ≥ 0`.
* `rank_one_case` — assembles these for the actual data, using `Kb_ne_zero` for `w ≠ 0`.
* `Wlift`, `Km_rank_one` — the lift of `w` to `W ∈ e^⊥ ⊆ ℝ³` via the basis dual to `(f₁,f₂)`,
  and the *full* matrix identity `K = W Wᵗ`.  That identity is forced: a symmetric `K` with
  `Ke = 0` is determined by the three pairings `fᵢᵗKfⱼ`.
* `ATb_eq` (`Aᵗb = ½b − Kc`), `sigma_of`, `Kc_eq_sigma_W` (`Kc = σW`), `sigma_sq` (`σ² = 1/12`),
  `BtW_eq` (`BᵗW = λW`), `WtA_eq` (`WᵗA = λWᵗ + σbᵗ`).
* `Ait`, `pk`, `qk`, `Ait_nonneg`, `pk_nonneg` (`pₖ = bᵗAᵏc ≥ 0`), `pk_zero`, `qk_zero`,
  `pk_succ` (`pₖ₊₁ = ½pₖ − σqₖ`), `qk_succ` (`qₖ₊₁ = σpₖ + λqₖ`).
* **`rank_one_impossible`** — setting `rₖ := 12σqₖ` (equal to `qₖ/σ`, but written as a product
  so no denominators arise) turns the pair into `rank_one_recursion`'s rational recursion,
  whose fifth iterate is negative, contradicting `pk_nonneg`.
* **`three_stage_rank_one_or_trichotomy`** — combining with `rank_dichotomy`: unconditionally,
  `θ = 1/2` or `θ ≥ 1`.

## The rank-two branch — closed

* `psd_kernel2`, `nilpotent_obstruction_coord` — the `θ = 1/2` obstruction.  The clean route:
  take any `u` with `y := B̄u ≠ 0`; then `B̄y = B̄²u = 0` by Cayley–Hamilton, so `yᵗQy = 0` and
  semidefiniteness gives `Qy = 0`; pairing `Qy = B̄ᵗK̄y` against `u` yields `yᵗK̄y = 0`,
  contradicting positive definiteness.  This needs **no case analysis** of the nilpotent `B̄`,
  unlike the `u vᵗ` factorization the note uses.
* `Bcols_const`, `Bbar_zero_impossible` — the degenerate `B̄ = 0` sub-case: then `B = e fᵗ`,
  `fᵗc = −1/12`, and `γ := min cᵢ` gives `γ² − γ/2 + 1/12 ≤ 0`, impossible.
* **`theta_half_impossible`**.
* `sharp_bound`, `beta_sum`, `theta_gt_one_arith`, `theta_gt_one_impossible_ordered` — the
  sharpened diagonal bound and the `θ > 1` endgame.  The endgame is stated over plain reals so
  that elaboration never unfolds `Data`.
* `relab`, `IsPerm3`, `relab_mem`, `permData` — full permutation-invariance of `Data`, built
  explicitly over `range 3` (every field is a three-term rearrangement).
* `theta_permData`, `detKb_permData` — `θ` and `det K̄` are permutation-invariant; the latter
  because the permutation fixes `e`, so the induced map on `ℝ³/⟨e⟩` has determinant `±1`.
* **`theta_gt_one_impossible`** — the ordering WLOG, with no assumption.

## Theorem 1

**`three_stage_claim_inconsistent`** : `¬ Nonempty Data`, and the unbundled
**`no_three_stage_tableau`** taking the tableau data as explicit arguments.

`rank_dichotomy` splits on `det K̄`.  Rank one is `rank_one_impossible`.  In the rank-two case
`theta_ge_half` and `sig2B_nonneg` are theorems, so `trichotomy_rank_two` leaves `θ = 1/2` or
`θ ≥ 1`; the branches are `theta_half_impossible`, `theta_one_impossible_rank_two`, and
`theta_gt_one_impossible`.  Nothing is assumed beyond the `Data` fields themselves.

Every inequality, every algebraic identity, both accretivity facts, the quotient form, the rank
dichotomy, the rank-one normal form and the three trace branches are machine-checked, with no
`sorry` and no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.
-/

open Finset

namespace SSP

namespace ThreeStage

/-- Hypotheses of the general Claim at `s = 3`, as a bundle.  An inhabitant would be a
counterexample; Theorem 1 of `s3_general_claim_proof.tex` says there is none. -/
structure Data where
  A : ℕ → ℕ → ℝ
  R : ℕ → ℕ → ℝ
  b : ℕ → ℝ
  c : ℕ → ℝ
  hA : ∀ i ∈ range 3, ∀ j ∈ range 3, 0 ≤ A i j
  hRsymm : ∀ i ∈ range 3, ∀ j ∈ range 3, R i j = R j i
  hRpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 3, ∑ j ∈ range 3, R i j * (x i * x j)
  hb : ∀ i ∈ range 3, b i = ∑ j ∈ range 3, R i j
  hbnn : ∀ i ∈ range 3, 0 ≤ b i
  hc : ∀ i ∈ range 3, c i = ∑ j ∈ range 3, A i j
  hMpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 3, ∑ j ∈ range 3,
    ((∑ k ∈ range 3, R i k * A k j) + (∑ k ∈ range 3, R j k * A k i) - b i * b j) * (x i * x j)
  h1 : ∑ i ∈ range 3, b i = 1
  h2 : ∑ i ∈ range 3, b i * c i = 1/2
  h3 : ∑ i ∈ range 3, b i * (c i)^2 = 1/3
  h4 : ∑ i ∈ range 3, b i * ∑ j ∈ range 3, A i j * c j = 1/6



variable (d : Data)

/-- Expand a `range 3` sum. -/
lemma sum3 (f : ℕ → ℝ) : ∑ i ∈ range 3, f i = f 0 + f 1 + f 2 := by
  simp [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ]

/-- **Lemma 1: at most one vanishing weight.**  If two weights vanish the third is `1`, and
then `bᵀc = 1/2` forces `c = 1/2` at that index while `bᵀc² = 1/3` forces `c² = 1/3`. -/
lemma not_two_zero (i j : ℕ) (hi : i ∈ range 3) (hj : j ∈ range 3) (hij : i ≠ j)
    (h0i : d.b i = 0) (h0j : d.b j = 0) : False := by
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  -- the third index k
  have e1 := d.h1; have e2 := d.h2; have e3 := d.h3
  rw [sum3] at e1 e2 e3
  interval_cases i <;> interval_cases j <;>
    first
      | exact hij rfl
      | (rw [h0i, h0j] at e1 e2 e3; nlinarith [e1, e2, e3])




/-- If a PSD form vanishes at `x`, then `M x = 0`.  Standard: the quadratic
`q(u) = (x+u t)ᵗ M (x+u t) ≥ 0` in `t` has a double root at `t=0`. -/
lemma psd_kernel {n : ℕ} (M : ℕ → ℕ → ℝ)
    (hsymm : ∀ i ∈ range n, ∀ j ∈ range n, M i j = M j i)
    (hpsd : ∀ y : ℕ → ℝ, 0 ≤ ∑ i ∈ range n, ∑ j ∈ range n, M i j * (y i * y j))
    (x : ℕ → ℝ) (hx : ∑ i ∈ range n, ∑ j ∈ range n, M i j * (x i * x j) = 0)
    (z : ℕ → ℝ) : ∑ i ∈ range n, ∑ j ∈ range n, M i j * (x i * z j) = 0 := by
  -- the cross term; use q(t) = Q(x) + 2t B(x,z) + t^2 Q(z) >= 0 with Q(x)=0
  set Bxz := ∑ i ∈ range n, ∑ j ∈ range n, M i j * (x i * z j) with hB
  set Qz := ∑ i ∈ range n, ∑ j ∈ range n, M i j * (z i * z j) with hQ
  have key : ∀ t : ℝ, 0 ≤ 2*t*Bxz + t^2*Qz := by
    intro t
    have h := hpsd (fun i => x i + t * z i)
    have expand : ∑ i ∈ range n, ∑ j ∈ range n,
        M i j * ((x i + t * z i) * (x j + t * z j))
        = (∑ i ∈ range n, ∑ j ∈ range n, M i j * (x i * x j))
          + t * ((∑ i ∈ range n, ∑ j ∈ range n, M i j * (x i * z j))
                 + (∑ i ∈ range n, ∑ j ∈ range n, M i j * (z i * x j)))
          + t^2 * (∑ i ∈ range n, ∑ j ∈ range n, M i j * (z i * z j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hswap : ∑ i ∈ range n, ∑ j ∈ range n, M i j * (z i * x j)
        = ∑ i ∈ range n, ∑ j ∈ range n, M i j * (x i * z j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i hi => ?_
      rw [hsymm j hj i hi]; ring
    rw [expand, hx, hswap] at h
    calc (0:ℝ) ≤ 0 + t * (Bxz + Bxz) + t^2 * Qz := by rw [hB, hQ] at *; linarith
      _ = 2*t*Bxz + t^2*Qz := by ring
  -- a linear-plus-quadratic nonneg for all `t` forces the linear coefficient to vanish
  rcases eq_or_ne Bxz 0 with hb | hb
  · exact hb
  exfalso
  have hB2 : 0 < Bxz^2 := by positivity
  have step : ∀ sc : ℝ, 0 < sc → 2 ≤ sc * Qz := by
    intro sc hs
    have h2 := key (-sc*Bxz)
    have hnn : 0 ≤ -2*sc*Bxz^2 + sc^2*Bxz^2*Qz := by
      calc (0:ℝ) ≤ 2*(-sc*Bxz)*Bxz + (-sc*Bxz)^2*Qz := h2
        _ = -2*sc*Bxz^2 + sc^2*Bxz^2*Qz := by ring
    have hsb : 0 < sc * Bxz^2 := by positivity
    nlinarith [hnn, hsb, hB2, hs]
  rcases (le_or_gt Qz 0) with hQ | hQ
  · have := step 1 one_pos; nlinarith
  · have := step (1/Qz) (by positivity)
    rw [one_div_mul_cancel (ne_of_gt hQ)] at this
    norm_num at this




/-- Column sums of `R` equal `b`, by symmetry plus `R e = b`. -/
lemma Rcol (k : ℕ) (hk : k ∈ range 3) : d.R 0 k + d.R 1 k + d.R 2 k = d.b k := by
  have hb := d.hb k hk
  rw [sum3] at hb
  have hk' := mem_range.1 hk
  interval_cases k
  · rw [d.hRsymm 1 (by simp) 0 (by simp), d.hRsymm 2 (by simp) 0 (by simp)]; linarith
  · rw [d.hRsymm 0 (by simp) 1 (by simp), d.hRsymm 2 (by simp) 1 (by simp)]; linarith
  · rw [d.hRsymm 0 (by simp) 2 (by simp), d.hRsymm 1 (by simp) 2 (by simp)]; linarith

/-- The quadratic form of `M` at the all-ones vector vanishes: `eᵗMe = 2bᵗc − (bᵗe)² = 0`. -/
lemma eMe_zero : ∑ i ∈ range 3, ∑ j ∈ range 3,
    ((∑ k ∈ range 3, d.R i k * d.A k j) + (∑ k ∈ range 3, d.R j k * d.A k i)
      - d.b i * d.b j) * ((fun _ => (1:ℝ)) i * (fun _ => (1:ℝ)) j) = 0 := by
  have k0 := Rcol d 0 (by simp); have k1 := Rcol d 1 (by simp); have k2 := Rcol d 2 (by simp)
  have c0 := d.hc 0 (by simp); have c1 := d.hc 1 (by simp); have c2 := d.hc 2 (by simp)
  rw [sum3] at c0 c1 c2
  have e1 := d.h1; have e2 := d.h2
  rw [sum3] at e1 e2
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  -- eᵗMe = 2 Σ_k (col_k R) c_k − (Σ b)²; substitute c_k = row sums of A and col = b
  linear_combination (2:ℝ)*e2 - (d.b 0 + d.b 1 + d.b 2 + 1)*e1
    + (2:ℝ)*(d.c 0*k0 + d.c 1*k1 + d.c 2*k2)
    - (2:ℝ)*((d.R 0 0 + d.R 1 0 + d.R 2 0)*c0 + (d.R 0 1 + d.R 1 1 + d.R 2 1)*c1
             + (d.R 0 2 + d.R 1 2 + d.R 2 2)*c2)



/-- `M` is symmetric. -/
lemma Msymm : ∀ i ∈ range 3, ∀ j ∈ range 3,
    ((∑ k ∈ range 3, d.R i k * d.A k j) + (∑ k ∈ range 3, d.R j k * d.A k i) - d.b i * d.b j)
    = ((∑ k ∈ range 3, d.R j k * d.A k i) + (∑ k ∈ range 3, d.R i k * d.A k j)
        - d.b j * d.b i) := by
  intro i _ j _; ring

/-- **Lemma 3: `M e = 0`.**  From `eᵗMe = 0` and `M ⪰ 0` via `psd_kernel`. -/
lemma Me_zero (z : ℕ → ℝ) : ∑ i ∈ range 3, ∑ j ∈ range 3,
    ((∑ k ∈ range 3, d.R i k * d.A k j) + (∑ k ∈ range 3, d.R j k * d.A k i)
      - d.b i * d.b j) * ((fun _ => (1:ℝ)) i * z j) = 0 :=
  psd_kernel _ (Msymm d) d.hMpsd (fun _ => 1) (eMe_zero d) z

/-- **The kernel identity `R c = b − Aᵗ b`, coordinatewise.**  Taking `z = eⱼ` in `Me_zero`
gives the `j`-th coordinate of `Me = Rc + Aᵗb − b = 0`. -/
lemma Rc_eq (j : ℕ) (hj : j ∈ range 3) :
    (∑ k ∈ range 3, d.R j k * d.c k) + (∑ i ∈ range 3, d.A i j * d.b i) = d.b j := by
  have h := Me_zero d (fun k => if k = j then 1 else 0)
  have hj' := mem_range.1 hj
  have k0 := Rcol d 0 (by simp); have k1 := Rcol d 1 (by simp); have k2 := Rcol d 2 (by simp)
  have c0 := d.hc 0 (by simp); have c1 := d.hc 1 (by simp); have c2 := d.hc 2 (by simp)
  rw [sum3] at c0 c1 c2
  have e1 := d.h1
  rw [sum3] at e1
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at h ⊢
  interval_cases j <;> norm_num at h ⊢
  · linear_combination h + d.R 0 0*c0 + d.R 0 1*c1 + d.R 0 2*c2
      - d.A 0 0*k0 - d.A 1 0*k1 - d.A 2 0*k2 + d.b 0*e1
  · linear_combination h + d.R 1 0*c0 + d.R 1 1*c1 + d.R 1 2*c2
      - d.A 0 1*k0 - d.A 1 1*k1 - d.A 2 1*k2 + d.b 1*e1
  · linear_combination h + d.R 2 0*c0 + d.R 2 1*c1 + d.R 2 2*c2
      - d.A 0 2*k0 - d.A 1 2*k1 - d.A 2 2*k2 + d.b 2*e1


/-- Cauchy–Schwarz for a PSD form: `(xᵗRy)² ≤ (xᵗRx)(yᵗRy)`. -/
lemma psd_cauchy {n : ℕ} (R : ℕ → ℕ → ℝ)
    (hsymm : ∀ i ∈ range n, ∀ j ∈ range n, R i j = R j i)
    (hpsd : ∀ z : ℕ → ℝ, 0 ≤ ∑ i ∈ range n, ∑ j ∈ range n, R i j * (z i * z j))
    (x y : ℕ → ℝ) :
    (∑ i ∈ range n, ∑ j ∈ range n, R i j * (x i * y j))^2
      ≤ (∑ i ∈ range n, ∑ j ∈ range n, R i j * (x i * x j))
        * (∑ i ∈ range n, ∑ j ∈ range n, R i j * (y i * y j)) := by
  set Bxy := ∑ i ∈ range n, ∑ j ∈ range n, R i j * (x i * y j) with hB
  set Qx := ∑ i ∈ range n, ∑ j ∈ range n, R i j * (x i * x j) with hQx
  set Qy := ∑ i ∈ range n, ∑ j ∈ range n, R i j * (y i * y j) with hQy
  have key : ∀ t : ℝ, 0 ≤ Qx + 2*t*Bxy + t^2*Qy := by
    intro t
    have h := hpsd (fun i => x i + t * y i)
    have expand : ∑ i ∈ range n, ∑ j ∈ range n,
        R i j * ((x i + t * y i) * (x j + t * y j))
        = Qx + t * ((∑ i ∈ range n, ∑ j ∈ range n, R i j * (x i * y j))
                    + (∑ i ∈ range n, ∑ j ∈ range n, R i j * (y i * x j)))
          + t^2 * Qy := by
      rw [hQx, hQy]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hswap : ∑ i ∈ range n, ∑ j ∈ range n, R i j * (y i * x j)
        = ∑ i ∈ range n, ∑ j ∈ range n, R i j * (x i * y j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i hi => ?_
      rw [hsymm j hj i hi]; ring
    rw [expand, hswap] at h
    calc (0:ℝ) ≤ Qx + t * (Bxy + Bxy) + t^2 * Qy := by rw [hB] at *; linarith
      _ = Qx + 2*t*Bxy + t^2*Qy := by ring
  -- discriminant of a nonneg quadratic
  have hQy0 : 0 ≤ Qy := by have := key 0; simpa using hpsd y
  rcases eq_or_lt_of_le hQy0 with h0 | hpos
  · -- `Qy = 0` forces `Bxy = 0`, by `psd_kernel` applied at `y`
    have hB0 : Bxy = 0 := by
      have hk := psd_kernel R hsymm hpsd y (by rw [← hQy, ← h0]) x
      -- `hk : Σ R i j (y i * x j) = 0`; swap to `Bxy`
      have hswap : ∑ i ∈ range n, ∑ j ∈ range n, R i j * (y i * x j)
          = ∑ i ∈ range n, ∑ j ∈ range n, R i j * (x i * y j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i hi => ?_
        rw [hsymm j hj i hi]; ring
      rw [hswap] at hk
      rw [hB]; exact hk
    rw [hB0, ← h0]; simp
  · have := key (-Bxy/Qy)
    have hne : Qy ≠ 0 := ne_of_gt hpos
    field_simp at this
    nlinarith [this, hpos]



/-- `eᵗRx = bᵗx`: the `R`-pairing against the all-ones vector is the `b`-pairing. -/
lemma eRx (x : ℕ → ℝ) :
    ∑ i ∈ range 3, ∑ j ∈ range 3, d.R i j * ((fun _ => (1:ℝ)) i * x j)
      = ∑ j ∈ range 3, d.b j * x j := by
  have k0 := Rcol d 0 (by simp); have k1 := Rcol d 1 (by simp); have k2 := Rcol d 2 (by simp)
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  linear_combination x 0 * k0 + x 1 * k1 + x 2 * k2

/-- `eᵗRe = 1`. -/
lemma eRe : ∑ i ∈ range 3, ∑ j ∈ range 3,
    d.R i j * ((fun _ => (1:ℝ)) i * (fun _ => (1:ℝ)) j) = 1 := by
  have h := eRx d (fun _ => 1)
  have e1 := d.h1
  simpa using h.trans (by simpa using e1)

/-- **Lemma 5: `K = R − b bᵗ ⪰ 0`.**  Cauchy–Schwarz in the `R`-semi-inner product:
`(bᵗx)² = (eᵗRx)² ≤ (eᵗRe)(xᵗRx) = xᵗRx`. -/
lemma K_psd (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range 3, ∑ j ∈ range 3, (d.R i j - d.b i * d.b j) * (x i * x j) := by
  have hcs := psd_cauchy d.R d.hRsymm d.hRpsd (fun _ => 1) x
  rw [eRx d x, eRe d] at hcs
  have hsplit : ∑ i ∈ range 3, ∑ j ∈ range 3, (d.R i j - d.b i * d.b j) * (x i * x j)
      = (∑ i ∈ range 3, ∑ j ∈ range 3, d.R i j * (x i * x j))
        - (∑ j ∈ range 3, d.b j * x j)^2 := by
    simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [hsplit]
  nlinarith [hcs]


/-- **Lemma 6 (redundancy): `cᵗRc = 1/3`.**  From `Rc = b − Aᵗb` we get
`bᵗAc = 1/2 − cᵗRc`, so `bᵗAc = 1/6` is equivalent to `cᵗRc = 1/3`. -/
lemma cRc : ∑ i ∈ range 3, ∑ j ∈ range 3, d.R i j * (d.c i * d.c j) = 1/3 := by
  have r0 := Rc_eq d 0 (by simp); have r1 := Rc_eq d 1 (by simp); have r2 := Rc_eq d 2 (by simp)
  have h2 := d.h2; have h4 := d.h4
  rw [sum3] at h2 h4
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at r0 r1 r2 h4 ⊢
  have hs0 := d.hRsymm 0 (by simp) 1 (by simp)
  have hs1 := d.hRsymm 0 (by simp) 2 (by simp)
  have hs2 := d.hRsymm 1 (by simp) 2 (by simp)
  linear_combination d.c 0 * r0 + d.c 1 * r1 + d.c 2 * r2 - h4 + (1:ℝ) * h2


/-- **Lemma 8: `cᵗKc = 1/12`.**  Since `cᵗΛc = Σbᵢcᵢ² − (bᵗc)² = 1/3 − 1/4 = 1/12` and
`cᵗRc = 1/3`, we get `cᵗKc = cᵗRc − (bᵗc)² = 1/3 − 1/4 = 1/12`. -/
lemma cKc : ∑ i ∈ range 3, ∑ j ∈ range 3, (d.R i j - d.b i * d.b j) * (d.c i * d.c j)
    = 1/12 := by
  have hR := cRc d
  have h2 := d.h2
  rw [sum3] at h2
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at hR ⊢
  linear_combination hR - (d.b 0*d.c 0 + d.b 1*d.c 1 + d.b 2*d.c 2 + 1/2) * h2

/-- `cᵗKc ≠ 0`: so `K` does not vanish on the quotient `ℝ³/⟨e⟩`.  This is what makes the
rank dichotomy of the note nontrivial. -/
lemma cKc_ne : ∑ i ∈ range 3, ∑ j ∈ range 3, (d.R i j - d.b i * d.b j) * (d.c i * d.c j)
    ≠ 0 := by
  rw [cKc d]; norm_num


/-- `K = R − b bᵗ`. -/
noncomputable def Km : ℕ → ℕ → ℝ := fun i j => d.R i j - d.b i * d.b j

/-- `B = A − c bᵗ`. -/
noncomputable def Bm : ℕ → ℕ → ℝ := fun i j => d.A i j - d.c i * d.b j

/-- `B e = 0`, since `A e = c` and `bᵗe = 1`. -/
lemma Bm_e (i : ℕ) (hi : i ∈ range 3) : ∑ j ∈ range 3, Bm d i j = 0 := by
  have hc := d.hc i hi
  have e1 := d.h1
  rw [sum3] at hc e1
  simp only [Bm, show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  linear_combination -hc - d.c i * e1

/-- `K e = 0`. -/
lemma Km_e (i : ℕ) (hi : i ∈ range 3) : ∑ j ∈ range 3, Km d i j = 0 := by
  have hb := d.hb i hi
  have e1 := d.h1
  rw [sum3] at hb e1
  simp only [Km, show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  linear_combination -hb - d.b i * e1

/-- **Lemma 9 (accretive form): `M = K B + Bᵗ K` entrywise.** -/
lemma M_factor (i j : ℕ) (hi : i ∈ range 3) (hj : j ∈ range 3) :
    (∑ k ∈ range 3, d.R i k * d.A k j) + (∑ k ∈ range 3, d.R j k * d.A k i) - d.b i * d.b j
      = (∑ k ∈ range 3, Km d i k * Bm d k j) + (∑ k ∈ range 3, Bm d k i * Km d k j) := by
  have ri := Rc_eq d i hi
  have rj := Rc_eq d j hj
  have ki := Km_e d i hi
  have kj := Km_e d j hj
  have h2 := d.h2
  rw [sum3] at h2
  have e1 := d.h1
  rw [sum3] at e1
  -- symmetry of R, needed to match Rⱼₖ with Rₖⱼ inside the BᵗK sum
  have s01 := d.hRsymm 0 (by simp) 1 (by simp)
  have s02 := d.hRsymm 0 (by simp) 2 (by simp)
  have s12 := d.hRsymm 1 (by simp) 2 (by simp)
  have hj' := mem_range.1 hj
  simp only [Km, Bm, show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero] at ri rj ki kj ⊢
  -- exact certificate: M − (KB+BᵗK) = bᵢ·rⱼ + bⱼ·rᵢ − 2(bᵗc − 1/2)·bᵢbⱼ
  interval_cases j
  · simp only [s01, s02] at ri rj ⊢
    linear_combination d.b i * rj + d.b 0 * ri - (2:ℝ) * d.b i * d.b 0 * h2
  · simp only [s01, s12] at ri rj ⊢
    linear_combination d.b i * rj + d.b 1 * ri - (2:ℝ) * d.b i * d.b 1 * h2
  · simp only [s02, s12] at ri rj ⊢
    linear_combination d.b i * rj + d.b 2 * ri - (2:ℝ) * d.b i * d.b 2 * h2


/-- **Lemma 12 (second-order test vector): `cᵗMc = 1/12 − 2 bᵗA²c`.**
Since `M ⪰ 0` this gives `bᵗA²c ≤ 1/24`. -/
lemma cMc : ∑ i ∈ range 3, ∑ j ∈ range 3,
    ((∑ k ∈ range 3, d.R i k * d.A k j) + (∑ k ∈ range 3, d.R j k * d.A k i)
      - d.b i * d.b j) * (d.c i * d.c j)
    = 1/12 - 2 * ∑ i ∈ range 3, d.b i * ∑ j ∈ range 3, d.A i j *
        (∑ k ∈ range 3, d.A j k * d.c k) := by
  have r0 := Rc_eq d 0 (by simp); have r1 := Rc_eq d 1 (by simp); have r2 := Rc_eq d 2 (by simp)
  have h2 := d.h2; have h4 := d.h4
  rw [sum3] at h2 h4
  have s01 := d.hRsymm 0 (by simp) 1 (by simp)
  have s02 := d.hRsymm 0 (by simp) 2 (by simp)
  have s12 := d.hRsymm 1 (by simp) 2 (by simp)
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero] at r0 r1 r2 h4 ⊢
  simp only [s01, s02, s12] at r0 r1 r2 ⊢
  -- cᵗMc = 2(Rc)ᵗ(Ac) − (bᵗc)² and (Rc)ᵗAc = bᵗAc − bᵗA²c
  linear_combination (2:ℝ)*h4 - (d.b 0*d.c 0 + d.b 1*d.c 1 + d.b 2*d.c 2 + 1/2)*h2
    + (2:ℝ)*((d.A 0 0*d.c 0 + d.A 0 1*d.c 1 + d.A 0 2*d.c 2)*r0
             + (d.A 1 0*d.c 0 + d.A 1 1*d.c 1 + d.A 1 2*d.c 2)*r1
             + (d.A 2 0*d.c 0 + d.A 2 1*d.c 1 + d.A 2 2*d.c 2)*r2)


/-- **Corollary of Lemma 12: `bᵗA²c ≤ 1/24`.**  Immediate from `cᵗMc ≥ 0`. -/
lemma bA2c_le : (∑ i ∈ range 3, d.b i * ∑ j ∈ range 3, d.A i j *
    (∑ k ∈ range 3, d.A j k * d.c k)) ≤ 1/24 := by
  have h := d.hMpsd d.c
  rw [cMc d] at h
  linarith


/-! ## The two endgame inequalities

These are the arithmetic cores of the note's two impossibility propositions, stated as
self-contained real-number facts.  Connecting them to `Data` needs the quotient-rank
dichotomy, which is not formalized here. -/

/-- **The rank-one recursion of the note's Proposition `rank1`.**  With
`p₀ = 1/2`, `r₀ = 1`, `pₖ₊₁ = ½pₖ − (1/12)rₖ`, `rₖ₊₁ = pₖ + λrₖ`, the fifth iterate is
`p₅ = −(144λ⁴+144λ³+72λ²+36λ+1)/1728`, which is negative for every `λ ≥ 0`.

Since the `pₖ = bᵗAᵏc` are all nonnegative (as `A ≥ 0`, `b ≥ 0`, `c = Ae ≥ 0`), this is the
contradiction that rules out the rank-one case. -/
lemma rank_one_recursion (lam p0 p1 p2 p3 p4 p5 r0 r1 r2 r3 r4 : ℝ)
    (hlam : 0 ≤ lam)
    (hp0 : p0 = 1/2) (hr0 : r0 = 1)
    (e1 : p1 = 1/2*p0 - 1/12*r0) (f1 : r1 = p0 + lam*r0)
    (e2 : p2 = 1/2*p1 - 1/12*r1) (f2 : r2 = p1 + lam*r1)
    (e3 : p3 = 1/2*p2 - 1/12*r2) (f3 : r3 = p2 + lam*r2)
    (e4 : p4 = 1/2*p3 - 1/12*r3) (f4 : r4 = p3 + lam*r3)
    (e5 : p5 = 1/2*p4 - 1/12*r4) :
    p5 < 0 := by
  subst hp0 hr0 e1 f1 e2 f2 e3 f3 e4 f4 e5
  nlinarith [hlam, sq_nonneg lam, sq_nonneg (lam^2), pow_nonneg hlam 3, pow_nonneg hlam 4]

/-- The closed form, for reference. -/
lemma rank_one_p5 (lam p0 p1 p2 p3 p4 p5 r0 r1 r2 r3 r4 : ℝ)
    (hp0 : p0 = 1/2) (hr0 : r0 = 1)
    (e1 : p1 = 1/2*p0 - 1/12*r0) (f1 : r1 = p0 + lam*r0)
    (e2 : p2 = 1/2*p1 - 1/12*r1) (f2 : r2 = p1 + lam*r1)
    (e3 : p3 = 1/2*p2 - 1/12*r2) (f3 : r3 = p2 + lam*r2)
    (e4 : p4 = 1/2*p3 - 1/12*r3) (f4 : r4 = p3 + lam*r3)
    (e5 : p5 = 1/2*p4 - 1/12*r4) :
    p5 = -(144*lam^4 + 144*lam^3 + 72*lam^2 + 36*lam + 1)/1728 := by
  subst hp0 hr0 e1 f1 e2 f2 e3 f3 e4 f4 e5
  ring


/-- **The rank-two endgame inequality of the note's Proposition `rank2`.**

With `g = (1/3 − c₁)/(1 − 2c₁)`, the quantity
`g(u−g) − ((c₁+u)/2 − 1/6 − c₁u)` factors as
`(12c₁²−6c₁+1)(6c₁u−3c₁−3u+1) / (18(2c₁−1)²)`.
For `0 ≤ c₁ ≤ 1/3` and `u > 1 − c₁` the first factor and the denominator are positive while
the last factor is negative, so the whole expression is negative — contradicting the necessary
condition `≥ 0` that `Δ ≥ 0` and the sharpened diagonal bound together force. -/
lemma rank_two_key (c1 u : ℝ) (_ : 0 ≤ c1) (hc3 : c1 ≤ 1/3) (hu : 1 - c1 < u) :
    ((1/3 - c1)/(1 - 2*c1)) * (u - (1/3 - c1)/(1 - 2*c1))
      - ((c1 + u)/2 - 1/6 - c1*u) < 0 := by
  have hden : (0:ℝ) < 1 - 2*c1 := by linarith
  have hne : (1 - 2*c1) ≠ 0 := ne_of_gt hden
  have hne2 : (2*c1 - 1) ≠ 0 := by intro h; apply hne; linarith
  have hsq : (0:ℝ) < 18*(2*c1 - 1)^2 := by
    have : (0:ℝ) < (2*c1 - 1)^2 := by positivity
    linarith
  -- the factorisation, cleared of denominators
  -- set `g` and use `g*(1-2c₁) = 1/3 - c₁` to avoid `field_simp` leaving inverses
  set g : ℝ := (1/3 - c1)/(1 - 2*c1) with hg
  have hgd : g * (1 - 2*c1) = 1/3 - c1 := by
    rw [hg, div_mul_cancel₀ _ hne]
  have hfac : g * (u - g) - ((c1 + u)/2 - 1/6 - c1*u)
      = (12*c1^2 - 6*c1 + 1) * (6*c1*u - 3*c1 - 3*u + 1) / (18*(2*c1 - 1)^2) := by
    rw [eq_div_iff (ne_of_gt hsq)]
    linear_combination (-6*(-6*c1*g + 6*c1*u - 3*c1 + 3*g - 3*u + 1)) * hgd
  rw [hfac]
  -- first factor positive (discriminant −12 < 0)
  have h1 : (0:ℝ) < 12*c1^2 - 6*c1 + 1 := by nlinarith [sq_nonneg (6*c1 - 1)]
  -- denominator positive
  have h2 : (0:ℝ) < 18*(2*c1 - 1)^2 := hsq
  -- last factor negative: strictly decreasing in `u` (slope `6c₁−3 < 0`), and at `u = 1−c₁`
  -- it equals `−2(3c₁²−3c₁+1) < 0`
  have h3 : 6*c1*u - 3*c1 - 3*u + 1 < 0 := by
    have hslope : 6*c1 - 3 < 0 := by linarith
    have hval : 6*c1*(1-c1) - 3*c1 - 3*(1-c1) + 1 = -2*(3*c1^2 - 3*c1 + 1) := by ring
    have hpos : (0:ℝ) < 3*c1^2 - 3*c1 + 1 := by nlinarith [sq_nonneg (2*c1 - 1)]
    nlinarith [hu, hslope, hval, hpos]
  exact div_neg_of_neg_of_pos (by nlinarith [h1, h3]) h2


/-! ## The trace trichotomy and the two degenerate obstructions -/

/-- Power-mean step: `Σdᵢ² ≥ θ²/3` for `θ = Σdᵢ`, with the explicit SOS witness. -/
lemma sum_sq_ge (d1 d2 d3 : ℝ) :
    (d1 + d2 + d3)^2 / 3 ≤ d1^2 + d2^2 + d3^2 := by
  nlinarith [sq_nonneg (d1 - d2), sq_nonneg (d1 - d3), sq_nonneg (d2 - d3)]

/-- Hence `Σ_{i<j} dᵢdⱼ ≤ θ²/3`. -/
lemma pair_sum_le (d1 d2 d3 : ℝ) :
    d1*d2 + d1*d3 + d2*d3 ≤ (d1 + d2 + d3)^2 / 3 := by
  nlinarith [sq_nonneg (d1 - d2), sq_nonneg (d1 - d3), sq_nonneg (d2 - d3)]

/-- **Proposition 14 (trace trichotomy).**  If `θ ≥ 1/2` (from `τ = θ − 1/2 ≥ 0`) and
`θ²/3 ≥ θ/2 − 1/6` (from `Δ ≥ 0` together with `σ₂(A) ≤ θ²/3`), then `θ = 1/2` or `θ ≥ 1`,
because `θ²/3 − (θ/2 − 1/6) = (2θ−1)(θ−1)/6`. -/
lemma trace_trichotomy (th : ℝ) (hlow : 1/2 ≤ th) (hquad : th/2 - 1/6 ≤ th^2/3) :
    th = 1/2 ∨ 1 ≤ th := by
  rcases eq_or_lt_of_le hlow with h | h
  · exact Or.inl h.symm
  · right
    by_contra hlt
    have hlt' : th < 1 := not_le.mp hlt
    have h1 : 0 < 2*th - 1 := by linarith
    have h2 : th - 1 < 0 := by linarith
    nlinarith [hquad, h1, h2]


/-- **Lemma 15 (nilpotency obstruction).**  If `X = u vᵗ` is a nonzero `2×2` nilpotent
(so `vᵗu = 0`) and `K` is positive definite, then `Q = KX + XᵗK` cannot be positive
semidefinite: `uᵗQu = 2(uᵗKu)(vᵗu) = 0` forces `Qu = 0`, but `Qu = (uᵗKu)v ≠ 0`. -/
lemma nilpotent_obstruction (Ku : ℝ) (hKu : 0 < Ku) (v0 v1 : ℝ) (hv : v0 ≠ 0 ∨ v1 ≠ 0)
    (Qu0 Qu1 : ℝ) (hQ0 : Qu0 = Ku * v0) (hQ1 : Qu1 = Ku * v1) :
    Qu0 ≠ 0 ∨ Qu1 ≠ 0 := by
  rcases hv with h | h
  · left; rw [hQ0]; exact mul_ne_zero (ne_of_gt hKu) h
  · right; rw [hQ1]; exact mul_ne_zero (ne_of_gt hKu) h

/-- **Lemma 16 (the degenerate case `B̄ = 0`).**  If `B = e fᵗ` with `fᵗe = 0`, then
`bᵗAc = 1/4 + fᵗc`, so `bᵗAc = 1/6` forces `fᵗc = −1/12`.  Setting `γ = min cᵢ ≥ 0` and
`g = f + γb ≥ 0`, one gets `gᵗe = γ` and `gᵗc = γ/2 − 1/12`, while `g ≥ 0` and `cᵢ ≥ γ` give
`gᵗc ≥ γ·gᵗe = γ²`.  Hence `γ² − γ/2 + 1/12 ≤ 0`, impossible since
`γ² − γ/2 + 1/12 = (γ − 1/4)² + 1/48 > 0`. -/
lemma Bzero_obstruction (gam : ℝ) (h : gam^2 - gam/2 + 1/12 ≤ 0) : False := by
  nlinarith [sq_nonneg (gam - 1/4)]

/-- The positive quantity behind Lemma 16. -/
lemma Bzero_quantity (gam : ℝ) : 0 < gam^2 - gam/2 + 1/12 := by
  nlinarith [sq_nonneg (gam - 1/4)]


/-! ## The `Δ`-identity and the trichotomy input -/

/-- The trace of `A`. -/
noncomputable def theta : ℝ := d.A 0 0 + d.A 1 1 + d.A 2 2

/-- The second elementary symmetric function of `A`, i.e. the sum of its principal
`2 × 2` minors. -/
noncomputable def sig2A : ℝ :=
  (d.A 0 0 * d.A 1 1 - d.A 0 1 * d.A 1 0)
    + (d.A 0 0 * d.A 2 2 - d.A 0 2 * d.A 2 0)
    + (d.A 1 1 * d.A 2 2 - d.A 1 2 * d.A 2 1)

/-- The same for `B = A − c bᵗ`. -/
noncomputable def sig2B : ℝ :=
  (Bm d 0 0 * Bm d 1 1 - Bm d 0 1 * Bm d 1 0)
    + (Bm d 0 0 * Bm d 2 2 - Bm d 0 2 * Bm d 2 0)
    + (Bm d 1 1 * Bm d 2 2 - Bm d 1 2 * Bm d 2 1)

/-- **`tr B = θ − 1/2`.**  Immediate from `tr B = tr A − bᵗc` and `bᵗc = 1/2`. -/
lemma trB : Bm d 0 0 + Bm d 1 1 + Bm d 2 2 = theta d - 1/2 := by
  have h2 := d.h2
  rw [sum3] at h2
  simp only [Bm, theta]
  linear_combination -h2

/-- **Lemma 17 (the `Δ`-identity): `σ₂(B) = σ₂(A) − θ·(bᵗc) + bᵗAc`.**  With `bᵗc = 1/2` and
`bᵗAc = 1/6` this reads `σ₂(B) = σ₂(A) − θ/2 + 1/6`. -/
lemma Delta_id : sig2B d = sig2A d - theta d / 2 + 1/6 := by
  have h2 := d.h2
  have h4 := d.h4
  rw [sum3] at h2 h4
  have c0 := d.hc 0 (by simp); have c1 := d.hc 1 (by simp); have c2 := d.hc 2 (by simp)
  rw [sum3] at c0 c1 c2
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at h4
  simp only [sig2B, sig2A, theta, Bm]
  linear_combination h4 - (d.A 0 0 + d.A 1 1 + d.A 2 2) * h2



/-- **`σ₂(A) ≤ θ²/3`.**  Since `A ≥ 0` the off-diagonal products `aᵢⱼaⱼᵢ` are nonnegative, so
`σ₂(A) ≤ Σ_{i<j} dᵢdⱼ`; then `pair_sum_le` gives the bound. -/
lemma sig2A_le : sig2A d ≤ (theta d)^2 / 3 := by
  have p01 := mul_nonneg (d.hA 0 (by simp) 1 (by simp)) (d.hA 1 (by simp) 0 (by simp))
  have p02 := mul_nonneg (d.hA 0 (by simp) 2 (by simp)) (d.hA 2 (by simp) 0 (by simp))
  have p12 := mul_nonneg (d.hA 1 (by simp) 2 (by simp)) (d.hA 2 (by simp) 1 (by simp))
  have hps := pair_sum_le (d.A 0 0) (d.A 1 1) (d.A 2 2)
  simp only [sig2A, theta]
  linarith [p01, p02, p12, hps]

/-- **The trichotomy hypothesis, assembled.**  Given accretivity (`τ ≥ 0` i.e. `θ ≥ 1/2`, and
`Δ ≥ 0`), the quadratic inequality of `trace_trichotomy` holds. -/
lemma trichotomy_input (htau : 1/2 ≤ theta d) (hDelta : 0 ≤ sig2B d) :
    theta d = 1/2 ∨ 1 ≤ theta d := by
  refine trace_trichotomy (theta d) htau ?_
  have hD := Delta_id d
  have hb := sig2A_le d
  linarith [hD, hb, hDelta]


/-! ## The diagonal bounds (Lemma 18) -/

/-- `c ≥ 0`, since `c = A e` and `A ≥ 0`. -/
lemma c_nonneg (i : ℕ) (hi : i ∈ range 3) : 0 ≤ d.c i := by
  have hc := d.hc i hi
  rw [sum3] at hc
  have h0 := d.hA i hi 0 (by simp)
  have h1 := d.hA i hi 1 (by simp)
  have h2 := d.hA i hi 2 (by simp)
  rw [hc]; linarith

/-- **Lemma 18 (diagonal bound): `aᵢᵢ ≤ cᵢ`.**  The diagonal entry is one summand of the
row sum, and the others are nonnegative. -/
lemma diag_le (i : ℕ) (hi : i ∈ range 3) : d.A i i ≤ d.c i := by
  have hc := d.hc i hi
  rw [sum3] at hc
  have hi' := mem_range.1 hi
  interval_cases i <;>
    [ (have h1 := d.hA 0 (by simp) 1 (by simp); have h2 := d.hA 0 (by simp) 2 (by simp));
      (have h0 := d.hA 1 (by simp) 0 (by simp); have h2 := d.hA 1 (by simp) 2 (by simp));
      (have h0 := d.hA 2 (by simp) 0 (by simp); have h1 := d.hA 2 (by simp) 1 (by simp)) ] <;>
    rw [hc] <;> linarith

/-- **The diagonal part of `bᵗAc` is at most `1/6`.**  Every term of
`bᵗAc = Σᵢ bᵢcᵢaᵢᵢ + Σ_{i≠j} bᵢaᵢⱼcⱼ` is nonnegative, so the diagonal part is at most the
total, which is `1/6`. -/
lemma diag_part_le : d.b 0 * d.c 0 * d.A 0 0 + d.b 1 * d.c 1 * d.A 1 1
    + d.b 2 * d.c 2 * d.A 2 2 ≤ 1/6 := by
  have h4 := d.h4
  rw [sum3] at h4
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at h4
  -- all six off-diagonal terms `bᵢ aᵢⱼ cⱼ` are nonnegative
  have t01 := mul_nonneg (mul_nonneg (d.hbnn 0 (by simp)) (d.hA 0 (by simp) 1 (by simp)))
    (c_nonneg d 1 (by simp))
  have t02 := mul_nonneg (mul_nonneg (d.hbnn 0 (by simp)) (d.hA 0 (by simp) 2 (by simp)))
    (c_nonneg d 2 (by simp))
  have t10 := mul_nonneg (mul_nonneg (d.hbnn 1 (by simp)) (d.hA 1 (by simp) 0 (by simp)))
    (c_nonneg d 0 (by simp))
  have t12 := mul_nonneg (mul_nonneg (d.hbnn 1 (by simp)) (d.hA 1 (by simp) 2 (by simp)))
    (c_nonneg d 2 (by simp))
  have t20 := mul_nonneg (mul_nonneg (d.hbnn 2 (by simp)) (d.hA 2 (by simp) 0 (by simp)))
    (c_nonneg d 0 (by simp))
  have t21 := mul_nonneg (mul_nonneg (d.hbnn 2 (by simp)) (d.hA 2 (by simp) 1 (by simp)))
    (c_nonneg d 1 (by simp))
  nlinarith [h4, t01, t02, t10, t12, t20, t21]


/-! ## The case `θ = 1` -/

/-- Equality in `pair_sum_le` forces all three entries equal. -/
lemma pair_sum_eq_imp (d1 d2 d3 : ℝ)
    (h : (d1 + d2 + d3)^2 / 3 ≤ d1*d2 + d1*d3 + d2*d3) :
    d1 = d2 ∧ d1 = d3 := by
  have hsos : (d1 + d2 + d3)^2/3 - (d1*d2 + d1*d3 + d2*d3)
      = ((d1-d2)^2 + (d1-d3)^2 + (d2-d3)^2)/6 := by ring
  have q12 := sq_nonneg (d1-d2)
  have q13 := sq_nonneg (d1-d3)
  have q23 := sq_nonneg (d2-d3)
  have h12 : (d1 - d2)^2 = 0 := by nlinarith [hsos, h, q12, q13, q23]
  have h13 : (d1 - d3)^2 = 0 := by nlinarith [hsos, h, q12, q13, q23]
  constructor
  · have h := sq_eq_zero_iff.mp h12; linarith
  · have h := sq_eq_zero_iff.mp h13; linarith

/-- **Proposition `sone` (`θ = 1` is impossible), the arithmetic core.**

At `θ = 1` the bounds `σ₂(A) ≥ 1/3` (from `Δ ≥ 0`) and `σ₂(A) ≤ θ²/3 = 1/3` force equality,
hence `a₀₀ = a₁₁ = a₂₂ = 1/3`.  Then the diagonal part of `bᵗAc` is `(1/3)·bᵗc = 1/6`, so
equality holds in the diagonal bound, forcing `bᵢaᵢⱼcⱼ = 0` off the diagonal.  Since
`cⱼ ≥ aⱼⱼ = 1/3 > 0`, that gives `aᵢⱼ = 0` for `i` in the support of `b`, whence `cᵢ = 1/3`
there and `bᵗc = 1/3`, contradicting `bᵗc = 1/2`.

Formalized here is the numerical heart: the diagonal entries are forced to `1/3`. -/
lemma theta_one_diag (hth : theta d = 1) (hDelta : 0 ≤ sig2B d) :
    d.A 0 0 = 1/3 ∧ d.A 1 1 = 1/3 ∧ d.A 2 2 = 1/3 := by
  have hD := Delta_id d
  have hle := sig2A_le d
  -- `Δ ≥ 0` with `θ = 1` gives `σ₂(A) ≥ 1/3`, and `sig2A_le` gives `σ₂(A) ≤ 1/3`
  have hge : (1:ℝ)/3 ≤ sig2A d := by rw [hth] at hD; linarith
  have hlt : sig2A d ≤ 1/3 := by rw [hth] at hle; linarith
  have heq : sig2A d = 1/3 := le_antisymm hlt hge
  -- so the pair-sum bound is tight; the off-diagonal products are nonnegative
  have p01 := mul_nonneg (d.hA 0 (by simp) 1 (by simp)) (d.hA 1 (by simp) 0 (by simp))
  have p02 := mul_nonneg (d.hA 0 (by simp) 2 (by simp)) (d.hA 2 (by simp) 0 (by simp))
  have p12 := mul_nonneg (d.hA 1 (by simp) 2 (by simp)) (d.hA 2 (by simp) 1 (by simp))
  have htight : (d.A 0 0 + d.A 1 1 + d.A 2 2)^2 / 3
      ≤ d.A 0 0 * d.A 1 1 + d.A 0 0 * d.A 2 2 + d.A 1 1 * d.A 2 2 := by
    have : theta d = d.A 0 0 + d.A 1 1 + d.A 2 2 := rfl
    rw [← this, hth]
    simp only [sig2A] at heq
    linarith [heq, p01, p02, p12]
  obtain ⟨e12, e13⟩ := pair_sum_eq_imp (d.A 0 0) (d.A 1 1) (d.A 2 2) htight
  have hsum : d.A 0 0 + d.A 1 1 + d.A 2 2 = 1 := hth
  refine ⟨by linarith, by linarith, by linarith⟩


set_option maxHeartbeats 1000000 in
/-- **`θ = 1` is impossible.**  The diagonal is forced to `1/3` each, so the diagonal part of
`bᵗAc` equals `(1/3)·bᵗc = 1/6`; combined with `diag_part_le` (which says that part is at most
`1/6`) every off-diagonal term `bᵢaᵢⱼcⱼ` must vanish.  Since `cⱼ ≥ aⱼⱼ = 1/3 > 0`, this forces
`bᵢaᵢⱼ = 0`; summing the row `i` then gives `bᵢcᵢ = bᵢ/3`, so `bᵗc = (1/3)bᵗe = 1/3`,
contradicting `bᵗc = 1/2`. -/
theorem theta_one_impossible (hth : theta d = 1) (hDelta : 0 ≤ sig2B d) : False := by
  obtain ⟨a0, a1, a2⟩ := theta_one_diag d hth hDelta
  -- cⱼ ≥ 1/3 for every j
  have hc0 : (1:ℝ)/3 ≤ d.c 0 := by have := diag_le d 0 (by simp); rw [a0] at this; linarith
  have hc1 : (1:ℝ)/3 ≤ d.c 1 := by have := diag_le d 1 (by simp); rw [a1] at this; linarith
  have hc2 : (1:ℝ)/3 ≤ d.c 2 := by have := diag_le d 2 (by simp); rw [a2] at this; linarith
  -- the diagonal part is exactly (1/3)·bᵗc = 1/6
  have h2 := d.h2
  rw [sum3] at h2
  have hdiag : d.b 0 * d.c 0 * d.A 0 0 + d.b 1 * d.c 1 * d.A 1 1
      + d.b 2 * d.c 2 * d.A 2 2 = 1/6 := by
    rw [a0, a1, a2]; linarith
  -- so every off-diagonal term vanishes
  have h4 := d.h4
  rw [sum3] at h4
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at h4
  have t01 := mul_nonneg (mul_nonneg (d.hbnn 0 (by simp)) (d.hA 0 (by simp) 1 (by simp)))
    (c_nonneg d 1 (by simp))
  have t02 := mul_nonneg (mul_nonneg (d.hbnn 0 (by simp)) (d.hA 0 (by simp) 2 (by simp)))
    (c_nonneg d 2 (by simp))
  have t10 := mul_nonneg (mul_nonneg (d.hbnn 1 (by simp)) (d.hA 1 (by simp) 0 (by simp)))
    (c_nonneg d 0 (by simp))
  have t12 := mul_nonneg (mul_nonneg (d.hbnn 1 (by simp)) (d.hA 1 (by simp) 2 (by simp)))
    (c_nonneg d 2 (by simp))
  have t20 := mul_nonneg (mul_nonneg (d.hbnn 2 (by simp)) (d.hA 2 (by simp) 0 (by simp)))
    (c_nonneg d 0 (by simp))
  have t21 := mul_nonneg (mul_nonneg (d.hbnn 2 (by simp)) (d.hA 2 (by simp) 1 (by simp)))
    (c_nonneg d 1 (by simp))
  -- the sum of the six nonnegative off-diagonal terms is 0
  have hoff : d.b 0 * d.A 0 1 * d.c 1 + d.b 0 * d.A 0 2 * d.c 2
      + d.b 1 * d.A 1 0 * d.c 0 + d.b 1 * d.A 1 2 * d.c 2
      + d.b 2 * d.A 2 0 * d.c 0 + d.b 2 * d.A 2 1 * d.c 1 = 0 := by
    linarith [h4, hdiag]
  -- hence each is 0; combine with cⱼ ≥ 1/3 > 0 to get bᵢaᵢⱼ = 0, then bᵢcᵢ = bᵢ/3
  have e01 : d.b 0 * d.A 0 1 * d.c 1 = 0 := by linarith
  have e02 : d.b 0 * d.A 0 2 * d.c 2 = 0 := by linarith
  have e10 : d.b 1 * d.A 1 0 * d.c 0 = 0 := by linarith
  have e12 : d.b 1 * d.A 1 2 * d.c 2 = 0 := by linarith
  have e20 : d.b 2 * d.A 2 0 * d.c 0 = 0 := by linarith
  have e21 : d.b 2 * d.A 2 1 * d.c 1 = 0 := by linarith
  -- bᵢcᵢ: row sums.  bᵢcᵢ = bᵢ(aᵢᵢ + Σ_{j≠i} aᵢⱼ) and bᵢaᵢⱼcⱼ = 0 with cⱼ>0 gives bᵢaᵢⱼ=0
  have r0 := d.hc 0 (by simp); have r1 := d.hc 1 (by simp); have r2 := d.hc 2 (by simp)
  rw [sum3] at r0 r1 r2
  have z01 : d.b 0 * d.A 0 1 = 0 := by
    rcases mul_eq_zero.mp e01 with h | h
    · exact h
    · linarith
  have z02 : d.b 0 * d.A 0 2 = 0 := by
    rcases mul_eq_zero.mp e02 with h | h
    · exact h
    · linarith
  have z10 : d.b 1 * d.A 1 0 = 0 := by
    rcases mul_eq_zero.mp e10 with h | h
    · exact h
    · linarith
  have z12 : d.b 1 * d.A 1 2 = 0 := by
    rcases mul_eq_zero.mp e12 with h | h
    · exact h
    · linarith
  have z20 : d.b 2 * d.A 2 0 = 0 := by
    rcases mul_eq_zero.mp e20 with h | h
    · exact h
    · linarith
  have z21 : d.b 2 * d.A 2 1 = 0 := by
    rcases mul_eq_zero.mp e21 with h | h
    · exact h
    · linarith
  -- bᵗc = Σ bᵢcᵢ = Σ bᵢ(aᵢᵢ) = (1/3)Σbᵢ = 1/3
  have e1 := d.h1
  rw [sum3] at e1
  rw [r0, r1, r2] at h2
  rw [a0, a1, a2] at h2
  linarith [h2, e1, z01, z02, z10, z12, z20, z21]


/-! ## Accretivity for a `2 × 2` block

If `K` is positive definite and `Q = K X + Xᵗ K` is positive semidefinite, then
`tr X ≥ 0` and `det X ≥ 0`.  Both are proved directly for `2 × 2`, with no eigenvalue
machinery: the trace from `tr(K⁻¹Q) = 2 tr X ≥ 0`, and the determinant by contradiction —
if `det X < 0` then `X` has a negative real eigenvalue, and its eigenvector `v` gives
`vᵗQv = 2λ(vᵗKv) < 0`.

Everything is in explicit coordinates: `K = ⟨k11, k12; k12, k22⟩`, `X = ⟨x11, x12; x21, x22⟩`.
-/

/-- The quadratic form of `Q = K X + Xᵗ K` at `(v1, v2)`. -/
noncomputable def Qform (k11 k12 k22 x11 x12 x21 x22 v1 v2 : ℝ) : ℝ :=
  2*(k11*x11 + k12*x21)*v1^2
    + 2*(k11*x12 + k12*x22 + k12*x11 + k22*x21)*v1*v2
    + 2*(k12*x12 + k22*x22)*v2^2

/-- `Qform` really is `vᵗ(KX + XᵗK)v`. -/
lemma Qform_eq (k11 k12 k22 x11 x12 x21 x22 v1 v2 : ℝ) :
    Qform k11 k12 k22 x11 x12 x21 x22 v1 v2
      = ((k11*x11 + k12*x21)*v1 + (k11*x12 + k12*x22)*v2) * v1
        + ((k12*x11 + k22*x21)*v1 + (k12*x12 + k22*x22)*v2) * v2
        + ((k11*x11 + k12*x21)*v1 + (k12*x11 + k22*x21)*v2) * v1
        + ((k11*x12 + k12*x22)*v1 + (k12*x12 + k22*x22)*v2) * v2 := by
  unfold Qform; ring

/-- **`det X ≥ 0`.**  If `det X < 0` the characteristic polynomial `λ² − (tr X)λ + det X` has
a negative root `λ`, and an eigenvector `v` for it gives `vᵗQv = 2λ(vᵗKv) < 0`.

Stated in the form actually needed: if some `v ≠ 0` satisfies `X v = λ v` with `λ < 0`, and
`K` is positive definite at `v`, then `Q` is not positive semidefinite. -/
lemma det_nonneg_of_accretive
    (k11 k12 k22 x11 x12 x21 x22 lam v1 v2 : ℝ)
    (hKv : 0 < k11*v1^2 + 2*k12*v1*v2 + k22*v2^2)
    (hlam : lam < 0)
    (he1 : x11*v1 + x12*v2 = lam*v1)
    (he2 : x21*v1 + x22*v2 = lam*v2) :
    Qform k11 k12 k22 x11 x12 x21 x22 v1 v2 < 0 := by
  have hexp : Qform k11 k12 k22 x11 x12 x21 x22 v1 v2
      = 2*lam*(k11*v1^2 + 2*k12*v1*v2 + k22*v2^2) := by
    unfold Qform
    linear_combination (2*k11*v1 + 2*k12*v2) * he1 + (2*k12*v1 + 2*k22*v2) * he2
  rw [hexp]
  have : 2*lam < 0 := by linarith
  exact mul_neg_of_neg_of_pos this hKv



/-- With `v = (x₁₂, λ − x₁₁)`, the first eigen-equation holds identically and the second
holds exactly when `λ` is a root of the characteristic polynomial. -/
lemma eigenvector_of_root (x11 x12 x21 x22 lam : ℝ)
    (hroot : lam^2 - (x11 + x22)*lam + (x11*x22 - x12*x21) = 0) :
    x11*x12 + x12*(lam - x11) = lam*x12
      ∧ x21*x12 + x22*(lam - x11) = lam*(lam - x11) := by
  constructor
  · ring
  · linear_combination -hroot

/-- **`det X ≥ 0` for an accretive `2 × 2` block, assuming `x₁₂ ≠ 0`.**

If `det X < 0` the discriminant `(x₁₁−x₂₂)² + 4x₁₂x₂₁ = (tr X)² − 4 det X` is positive, so the
characteristic polynomial has the real root `λ = (tr − √disc)/2`, which is negative because
`λ·(tr − λ) = det < 0` and `λ` is the smaller root.  The eigenvector `v = (x₁₂, λ − x₁₁)` is
nonzero (its first entry is `x₁₂ ≠ 0`), and `vᵗQv = 2λ(vᵗKv) < 0`. -/
lemma det_nonneg_accretive_generic
    (k11 k12 k22 x11 x12 x21 x22 : ℝ)
    (hx12 : x12 ≠ 0)
    (hKpd : ∀ w1 w2 : ℝ, (w1 ≠ 0 ∨ w2 ≠ 0) → 0 < k11*w1^2 + 2*k12*w1*w2 + k22*w2^2)
    (hQ : ∀ v1 v2 : ℝ, 0 ≤ Qform k11 k12 k22 x11 x12 x21 x22 v1 v2) :
    0 ≤ x11*x22 - x12*x21 := by
  by_contra hneg
  have hdet : x11*x22 - x12*x21 < 0 := by linarith
  set tr : ℝ := x11 + x22 with htr
  set dt : ℝ := x11*x22 - x12*x21 with hdt
  have hdisc : 0 < tr^2 - 4*dt := by nlinarith [sq_nonneg tr, hdet]
  set s : ℝ := Real.sqrt (tr^2 - 4*dt) with hs
  have hs2 : s^2 = tr^2 - 4*dt := Real.sq_sqrt (le_of_lt hdisc)
  have hspos : 0 < s := Real.sqrt_pos.mpr hdisc
  set lam : ℝ := (tr - s)/2 with hlam
  -- λ is a root
  have hroot : lam^2 - tr*lam + dt = 0 := by
    rw [hlam]; field_simp; linear_combination hs2
  -- λ < 0 : λ(tr − λ) = dt < 0 and tr − λ = (tr+s)/2 ≥ λ, so λ must be the negative factor
  have hprod : lam * (tr - lam) = dt := by rw [hlam]; field_simp; linear_combination -hs2
  have hlamneg : lam < 0 := by
    rcases lt_trichotomy lam 0 with h | h | h
    · exact h
    · rw [h] at hprod; simp at hprod; linarith [hprod, hdet]
    · -- λ > 0 forces tr − λ < 0, i.e. λ > tr; but λ = (tr−s)/2 < tr/2 ≤ tr when tr ≥ 0
      exfalso
      have h1 : tr - lam < 0 := by
        by_contra hc
        have : 0 ≤ lam * (tr - lam) := mul_nonneg (le_of_lt h) (by linarith [not_lt.mp hc])
        linarith [hprod, hdet]
      -- λ > 0 and tr − λ < 0 give tr < λ = (tr−s)/2, i.e. tr < −s < 0, so λ = (tr−s)/2 < 0
      have h2 : tr < lam := by linarith
      rw [hlam] at h2
      nlinarith [h2, hspos]
  have hroot' : lam^2 - (x11 + x22)*lam + (x11*x22 - x12*x21) = 0 := by
    rw [htr, hdt] at hroot; exact hroot
  obtain ⟨he1, he2⟩ := eigenvector_of_root x11 x12 x21 x22 lam hroot'
  have hKv := hKpd x12 (lam - x11) (Or.inl hx12)
  have := det_nonneg_of_accretive k11 k12 k22 x11 x12 x21 x22 lam x12 (lam - x11) hKv hlamneg he1 he2
  linarith [hQ x12 (lam - x11), this]


/-- **`tr X ≥ 0` for an accretive `2 × 2` block.**

The identity `tr(adj(K)·Q) = 2·det(K)·tr X` holds for `Q = KX + XᵗK`, and `adj(K)` admits the
explicit Cholesky factorization `adj(K) = vvᵗ + wwᵗ` with

  `v = (√k₂₂, −k₁₂/√k₂₂)`,   `w = (0, √(det K / k₂₂))`,

valid when `k₂₂ > 0`.  Hence `2·det(K)·tr X = Q(v) + Q(w) ≥ 0`, and `det K > 0` gives
`tr X ≥ 0`. -/
lemma trace_nonneg_accretive
    (k11 k12 k22 x11 x12 x21 x22 : ℝ)
    (hk22 : 0 < k22) (hdet : 0 < k11*k22 - k12^2)
    (hQ : ∀ v1 v2 : ℝ, 0 ≤ Qform k11 k12 k22 x11 x12 x21 x22 v1 v2) :
    0 ≤ x11 + x22 := by
  set a : ℝ := Real.sqrt k22 with ha
  set e : ℝ := Real.sqrt ((k11*k22 - k12^2)/k22) with he
  have ha2 : a^2 = k22 := Real.sq_sqrt (le_of_lt hk22)
  have hapos : 0 < a := Real.sqrt_pos.mpr hk22
  have hane : a ≠ 0 := ne_of_gt hapos
  have he2 : e^2 = (k11*k22 - k12^2)/k22 :=
    Real.sq_sqrt (le_of_lt (div_pos hdet hk22))
  -- the two Q-forms
  have h1 := hQ a (-k12/a)
  -- rewrite the first form with `a·(−k12/a) = −k12` and `a² = k22` up front
  have hkey : Qform k11 k12 k22 x11 x12 x21 x22 a (-k12/a)
      = 2*(k11*x11 + k12*x21)*k22 - 2*(k11*x12 + k12*x22 + k12*x11 + k22*x21)*k12
        + 2*(k12*x12 + k22*x22)*(k12^2/k22) := by
    unfold Qform
    rw [← ha2]
    field_simp
    ring
  have h2 := hQ 0 e
  -- their sum is 2·det(K)·tr X
  have hkey2 : Qform k11 k12 k22 x11 x12 x21 x22 0 e
      = 2*(k12*x12 + k22*x22)*((k11*k22 - k12^2)/k22) := by
    unfold Qform
    rw [← he2]; ring
  have hsum : Qform k11 k12 k22 x11 x12 x21 x22 a (-k12/a)
      + Qform k11 k12 k22 x11 x12 x21 x22 0 e
      = 2*(k11*k22 - k12^2)*(x11 + x22) := by
    rw [hkey, hkey2]
    field_simp
    ring
  have hpos : 0 < 2*(k11*k22 - k12^2) := by linarith
  nlinarith [h1, h2, hsum, hpos]


/-! ## Coordinates on the quotient `ℝ³/⟨e⟩`

We use the explicit complement basis `f₁ = (1,−1,0)`, `f₂ = (0,1,−1)`; together with `e` these
span `ℝ³` (the determinant is `3`).  Since `K e = 0`, the form of `K` descends, and its matrix
in this basis is `K̄ᵢⱼ = fᵢᵗ K fⱼ`. -/

/-- The first complement basis vector `f₁ = (1,−1,0)`. -/
noncomputable def f1 : ℕ → ℝ := fun i => if i = 0 then 1 else if i = 1 then -1 else 0

/-- The second complement basis vector `f₂ = (0,1,−1)`. -/
noncomputable def f2 : ℕ → ℝ := fun i => if i = 1 then 1 else if i = 2 then -1 else 0

/-- The `K`-pairing of two vectors. -/
noncomputable def Kpair (x y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range 3, ∑ j ∈ range 3, Km d i j * (x i * y j)

/-- `K̄` in the basis `(f₁, f₂)`: the three independent entries. -/
noncomputable def kb11 : ℝ := Kpair d f1 f1
noncomputable def kb12 : ℝ := Kpair d f1 f2
noncomputable def kb22 : ℝ := Kpair d f2 f2

/-- The quotient form is symmetric. -/
lemma Kpair_symm (x y : ℕ → ℝ) : Kpair d x y = Kpair d y x := by
  unfold Kpair Km
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i hi => ?_
  rw [d.hRsymm j hj i hi]; ring

/-- **`K̄ ⪰ 0`**: the quotient form is positive semidefinite, since it is the restriction of
`K ⪰ 0` to the span of `f₁, f₂`. -/
lemma Kb_psd (t1 t2 : ℝ) : 0 ≤ kb11 d * t1^2 + 2 * kb12 d * t1 * t2 + kb22 d * t2^2 := by
  have h := K_psd d (fun i => t1 * f1 i + t2 * f2 i)
  have hexp : ∑ i ∈ range 3, ∑ j ∈ range 3,
      (d.R i j - d.b i * d.b j) * ((t1 * f1 i + t2 * f2 i) * (t1 * f1 j + t2 * f2 j))
      = kb11 d * t1^2 + 2 * kb12 d * t1 * t2 + kb22 d * t2^2 := by
    have s01 := d.hRsymm 0 (by simp) 1 (by simp)
    have s02 := d.hRsymm 0 (by simp) 2 (by simp)
    have s12 := d.hRsymm 1 (by simp) 2 (by simp)
    simp only [kb11, kb12, kb22, Kpair, Km, f1, f2,
      show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    linear_combination (-t1*t2)*s01 + (t1*t2)*s02 + (-t1*t2)*s12
  rw [← hexp]
  exact h


/-- The quotient coordinates of `c` in the basis `(f₁, f₂)`: writing
`c = α e + s₁ f₁ + s₂ f₂`, one has `s₁ = (2c₀ − c₁ − c₂)/3` and `s₂ = (c₀ + c₁ − 2c₂)/3`. -/
noncomputable def s1c : ℝ := (2*d.c 0 - d.c 1 - d.c 2)/3

/-- The second quotient coordinate of `c`. -/
noncomputable def s2c : ℝ := (d.c 0 + d.c 1 - 2*d.c 2)/3

/-- `c` really decomposes as `α e + s₁ f₁ + s₂ f₂`, with `α = (c₀+c₁+c₂)/3`. -/
lemma c_decomp (i : ℕ) (hi : i ∈ range 3) :
    d.c i = (d.c 0 + d.c 1 + d.c 2)/3 + s1c d * f1 i + s2c d * f2 i := by
  have hi' := mem_range.1 hi
  interval_cases i <;> simp only [s1c, s2c, f1, f2] <;> norm_num <;> ring

/-- **`K̄` does not vanish**: evaluating the quotient form at the coordinates of `c` gives
`cᵗKc = 1/12 ≠ 0`, because `K e = 0` kills the `e`-component. -/
lemma Kb_ne_zero :
    kb11 d * (s1c d)^2 + 2 * kb12 d * (s1c d) * (s2c d) + kb22 d * (s2c d)^2 = 1/12 := by
  have hK := cKc d
  have k0 := Km_e d 0 (by simp); have k1 := Km_e d 1 (by simp); have k2 := Km_e d 2 (by simp)
  have s01 := d.hRsymm 0 (by simp) 1 (by simp)
  have s02 := d.hRsymm 0 (by simp) 2 (by simp)
  have s12 := d.hRsymm 1 (by simp) 2 (by simp)
  simp only [kb11, kb12, kb22, Kpair, Km, f1, f2, s1c, s2c,
    show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at hK k0 k1 k2 ⊢
  norm_num at hK k0 k1 k2 ⊢
  linear_combination hK + (-5*d.c 0^2/9 - 4*d.c 0*d.c 1/9 - 4*d.c 0*d.c 2/9 + d.c 1^2/9 + 2*d.c 1*d.c 2/9 + d.c 2^2/9)*k0 + (d.c 0^2/9 - 4*d.c 0*d.c 1/9 + 2*d.c 0*d.c 2/9 - 5*d.c 1^2/9 - 4*d.c 1*d.c 2/9 + d.c 2^2/9)*k1 + (d.c 0^2/9 + 2*d.c 0*d.c 1/9 - 4*d.c 0*d.c 2/9 + d.c 1^2/9 - 4*d.c 1*d.c 2/9 - 5*d.c 2^2/9)*k2
    + (5*d.c 0^2/9 + d.c 0*d.c 1/9 - 2*d.c 0*d.c 2/9 - 4*d.c 1^2/9 - 2*d.c 1*d.c 2/9
        + 2*d.c 2^2/9)*s01 + (d.c 0^2/9 + 2*d.c 0*d.c 1/9 + 5*d.c 0*d.c 2/9 + d.c 1^2/9
        - 4*d.c 1*d.c 2/9 - 5*d.c 2^2/9)*s02 + (2*d.c 0^2/9 + 4*d.c 0*d.c 1/9
        - 8*d.c 0*d.c 2/9 + 2*d.c 1^2/9 + d.c 1*d.c 2/9 - d.c 2^2/9)*s12


/-- **The rank dichotomy.**  `K̄` is a PSD `2 × 2` form which is not identically zero
(it takes the value `1/12` at the quotient coordinates of `c`).  So either its determinant is
positive — the rank-two case, where `K̄ ≻ 0` — or it vanishes, the rank-one case. -/
lemma rank_dichotomy :
    0 < kb11 d * kb22 d - (kb12 d) ^ 2 ∨ kb11 d * kb22 d - (kb12 d) ^ 2 = 0 := by
  -- a PSD 2×2 form has nonnegative determinant
  have hdet : 0 ≤ kb11 d * kb22 d - (kb12 d) ^ 2 := by
    have h11 : 0 ≤ kb11 d := by
      have := Kb_psd d 1 0; linarith
    have h22 : 0 ≤ kb22 d := by
      have := Kb_psd d 0 1; linarith
    rcases eq_or_lt_of_le h11 with h | h
    · -- kb11 = 0 forces kb12 = 0 (else the form is negative somewhere)
      have h12 : kb12 d = 0 := by
        -- with kb11 = 0 the form is `2 kb12 t1 t2 + kb22 t2²`; nonneg for all t1 forces kb12 = 0
        by_contra hne
        have key : ∀ t : ℝ, 0 ≤ 2 * kb12 d * t + kb22 d := by
          intro t
          have := Kb_psd d t 1
          rw [← h] at this
          nlinarith [this]
        have hnz : (2 * kb12 d) ≠ 0 := by intro hz; apply hne; linarith [hz]
        have := key (-(kb22 d + 1)/(2 * kb12 d))
        rw [show 2 * kb12 d * (-(kb22 d + 1)/(2 * kb12 d)) = -(kb22 d + 1) from by
          field_simp] at this
        linarith
      rw [← h, h12]; norm_num
    · -- kb11 > 0: complete the square
      have := Kb_psd d (-(kb12 d)/(kb11 d)) 1
      have hne : kb11 d ≠ 0 := ne_of_gt h
      field_simp at this
      nlinarith [this, h]
  rcases eq_or_lt_of_le hdet with h | h
  · exact Or.inr h.symm
  · exact Or.inl h

/-- In the rank-two case `K̄` is positive definite. -/
lemma Kb_pd_of_rank_two (hdet : 0 < kb11 d * kb22 d - (kb12 d) ^ 2) (t1 t2 : ℝ)
    (hne : t1 ≠ 0 ∨ t2 ≠ 0) :
    0 < kb11 d * t1^2 + 2 * kb12 d * t1 * t2 + kb22 d * t2^2 := by
  have h11 : 0 < kb11 d := by
    have h := Kb_psd d 1 0
    rcases eq_or_lt_of_le (by linarith [h] : (0:ℝ) ≤ kb11 d) with h0 | h0
    · exfalso; rw [← h0] at hdet; nlinarith [hdet, sq_nonneg (kb12 d)]
    · exact h0
  have hsos : kb11 d * (kb11 d * t1^2 + 2 * kb12 d * t1 * t2 + kb22 d * t2^2)
      = (kb11 d * t1 + kb12 d * t2)^2 + (kb11 d * kb22 d - (kb12 d) ^ 2) * t2^2 := by ring
  rcases hne with h | h
  · rcases eq_or_ne t2 0 with h2 | h2
    · rw [h2] at hsos ⊢
      have : 0 < (kb11 d * t1)^2 := by positivity
      nlinarith [hsos, h11, this]
    · have hp : 0 < (kb11 d * kb22 d - (kb12 d) ^ 2) * t2^2 := by positivity
      nlinarith [hsos, h11, hp, sq_nonneg (kb11 d * t1 + kb12 d * t2)]
  · have hp : 0 < (kb11 d * kb22 d - (kb12 d) ^ 2) * t2^2 := by
      have : 0 < t2^2 := by positivity
      positivity
    nlinarith [hsos, h11, hp, sq_nonneg (kb11 d * t1 + kb12 d * t2)]


/-! ## The quotient of `B`, and accretivity on the quotient

`B e = 0`, so `B` descends to the quotient `ℝ³/⟨e⟩`.  In the basis `(f₁, f₂)` its matrix `B̄`
has the entries below (each is the `f₁`- resp. `f₂`-coordinate of `B fⱼ` in the basis
`(e, f₁, f₂)`, whose determinant is `3`).  Two invariants come out clean:

  `tr B̄ = tr B = θ − 1/2`   and   `det B̄ = σ₂(B) = Δ`,

so the quotient is exactly where the trichotomy on `θ` lives.  Combined with `K̄ ⪰ 0` (and
`K̄ ≻ 0` in the rank-two case) and the descended `M ⪰ 0`, the accretivity lemmas
`trace_nonneg_accretive` and `det_nonneg_accretive_generic` now discharge `θ ≥ 1/2`
and `Δ ≥ 0` unconditionally. -/

/-- `B̄₁₁`: the `f₁`-coordinate of `B f₁`. -/
noncomputable def xb11 : ℝ :=
  (2*Bm d 0 0 - 2*Bm d 0 1 - Bm d 1 0 + Bm d 1 1 - Bm d 2 0 + Bm d 2 1)/3

/-- `B̄₁₂`: the `f₁`-coordinate of `B f₂`. -/
noncomputable def xb12 : ℝ :=
  (2*Bm d 0 0 + 4*Bm d 0 1 - Bm d 1 0 - 2*Bm d 1 1 - Bm d 2 0 - 2*Bm d 2 1)/3

/-- `B̄₂₁`: the `f₂`-coordinate of `B f₁`. -/
noncomputable def xb21 : ℝ :=
  (Bm d 0 0 - Bm d 0 1 + Bm d 1 0 - Bm d 1 1 - 2*Bm d 2 0 + 2*Bm d 2 1)/3

/-- `B̄₂₂`: the `f₂`-coordinate of `B f₂`. -/
noncomputable def xb22 : ℝ :=
  (Bm d 0 0 + 2*Bm d 0 1 + Bm d 1 0 + 2*Bm d 1 1 - 2*Bm d 2 0 - 4*Bm d 2 1)/3

/-- **`tr B̄ = tr B = θ − 1/2`.**  The quotient trace agrees with the full trace because
`B e = 0` means the `e`-eigenvalue of `B` is `0`. -/
lemma trace_xb : xb11 d + xb22 d = theta d - 1/2 := by
  have h := trB d
  have b0 := Bm_e d 0 (by simp)
  have b1 := Bm_e d 1 (by simp)
  have b2 := Bm_e d 2 (by simp)
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at b0 b1 b2
  simp only [xb11, xb22]
  linear_combination h - b2

/-- **`det B̄ = σ₂(B) = Δ`.**  Again because the third eigenvalue of `B` is `0`, so the
second elementary symmetric function of `B` is the determinant of the quotient. -/
lemma det_xb : xb11 d * xb22 d - xb12 d * xb21 d = sig2B d := by
  have b0 := Bm_e d 0 (by simp)
  have b1 := Bm_e d 1 (by simp)
  have b2 := Bm_e d 2 (by simp)
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at b0 b1 b2
  simp only [xb11, xb12, xb21, xb22, sig2B]
  linear_combination (Bm d 2 0)*b0 + (Bm d 2 1)*b1 + (-Bm d 0 0 - Bm d 1 1)*b2

/-- **The `M`-form descends**: at `v = t₁f₁ + t₂f₂` the quadratic form of `M = KB + BᵗK`
equals `Qform` of the quotient pair `(K̄, B̄)` at `(t₁, t₂)`. -/
lemma Mform_quotient (t1 t2 : ℝ) :
    ∑ i ∈ range 3, ∑ j ∈ range 3,
      ((∑ k ∈ range 3, d.R i k * d.A k j) + (∑ k ∈ range 3, d.R j k * d.A k i)
        - d.b i * d.b j) * ((t1 * f1 i + t2 * f2 i) * (t1 * f1 j + t2 * f2 j))
      = Qform (kb11 d) (kb12 d) (kb22 d) (xb11 d) (xb12 d) (xb21 d) (xb22 d) t1 t2 := by
  have mf : ∀ i ∈ range 3, ∀ j ∈ range 3,
      (∑ k ∈ range 3, d.R i k * d.A k j) + (∑ k ∈ range 3, d.R j k * d.A k i)
        - d.b i * d.b j
      = (∑ k ∈ range 3, Km d i k * Bm d k j) + (∑ k ∈ range 3, Bm d k i * Km d k j) :=
    fun i hi j hj => M_factor d i j hi hj
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => by
    rw [mf i hi j hj]))]
  have be0 := Bm_e d 0 (by simp)
  have be1 := Bm_e d 1 (by simp)
  have be2 := Bm_e d 2 (by simp)
  have ke0 := Km_e d 0 (by simp)
  have ke1 := Km_e d 1 (by simp)
  have ke2 := Km_e d 2 (by simp)
  have ks01 : Km d 0 1 = Km d 1 0 := by
    simp only [Km]; rw [d.hRsymm 0 (by simp) 1 (by simp)]; ring
  have ks02 : Km d 0 2 = Km d 2 0 := by
    simp only [Km]; rw [d.hRsymm 0 (by simp) 2 (by simp)]; ring
  have ks12 : Km d 1 2 = Km d 2 1 := by
    simp only [Km]; rw [d.hRsymm 1 (by simp) 2 (by simp)]; ring
  simp only [kb11, kb12, kb22, Kpair, xb11, xb12, xb21, xb22, Qform, f1, f2,
    show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    at be0 be1 be2 ke0 ke1 ke2 ⊢
  norm_num at be0 be1 be2 ke0 ke1 ke2 ⊢
  linear_combination (-2*(Km d 0 0)*t1*t2 + (Km d 0 1)*t1*t2 - (Km d 0 1)*t2^2 + (Km d 0 2)*t2^2
      + (Km d 1 0)*t1*t2 - (Km d 1 0)*t2^2 + (Km d 2 0)*t2^2)*be0
    + (-(Km d 0 1)*t1*t2 - (Km d 1 0)*t1*t2 + 2*(Km d 1 1)*t1*t2 - 2*(Km d 1 1)*t2^2
        + (Km d 1 2)*t2^2 + (Km d 2 1)*t2^2)*be1
    + (-(Km d 0 2)*t1*t2 + (Km d 1 2)*t1*t2 - (Km d 1 2)*t2^2 - (Km d 2 0)*t1*t2
        + (Km d 2 1)*t1*t2 - (Km d 2 1)*t2^2 + 2*(Km d 2 2)*t2^2)*be2
    + (2*(Bm d 0 0)*t1^2/3 + 2*(Bm d 0 0)*t1*t2/3 - 2*(Bm d 0 1)*t1^2/3
        + 4*(Bm d 0 1)*t1*t2/3 + 2*(Bm d 1 0)*t1^2/3 + 2*(Bm d 1 0)*t1*t2/3
        - 2*(Bm d 1 1)*t1^2/3 + 4*(Bm d 1 1)*t1*t2/3 + 2*(Bm d 2 0)*t1^2/3
        + 2*(Bm d 2 0)*t1*t2/3 - 2*(Bm d 2 1)*t1^2/3 + 4*(Bm d 2 1)*t1*t2/3)*ke0
    + (-2*(Bm d 0 0)*t1^2/3 + 2*(Bm d 0 0)*t2^2/3 + 2*(Bm d 0 1)*t1^2/3
        - 2*(Bm d 0 1)*t1*t2 + 4*(Bm d 0 1)*t2^2/3 - 2*(Bm d 1 0)*t1^2/3
        + 2*(Bm d 1 0)*t2^2/3 + 2*(Bm d 1 1)*t1^2/3 - 2*(Bm d 1 1)*t1*t2
        + 4*(Bm d 1 1)*t2^2/3 - 2*(Bm d 2 0)*t1^2/3 + 2*(Bm d 2 0)*t2^2/3
        + 2*(Bm d 2 1)*t1^2/3 - 2*(Bm d 2 1)*t1*t2 + 4*(Bm d 2 1)*t2^2/3)*ke1
    + (-2*(Bm d 0 0)*t1*t2/3 - 2*(Bm d 0 0)*t2^2/3 + 2*(Bm d 0 1)*t1*t2/3
        - 4*(Bm d 0 1)*t2^2/3 - 2*(Bm d 1 0)*t1*t2/3 - 2*(Bm d 1 0)*t2^2/3
        + 2*(Bm d 1 1)*t1*t2/3 - 4*(Bm d 1 1)*t2^2/3 - 2*(Bm d 2 0)*t1*t2/3
        - 2*(Bm d 2 0)*t2^2/3 + 2*(Bm d 2 1)*t1*t2/3 - 4*(Bm d 2 1)*t2^2/3)*ke2
    + (-(Bm d 0 0)*t1^2 - 4*(Bm d 0 0)*t1*t2/3 - (Bm d 0 0)*t2^2/3 + (Bm d 0 1)*t1^2
        - 5*(Bm d 0 1)*t1*t2/3 - 2*(Bm d 0 1)*t2^2/3 - (Bm d 1 0)*t1^2 - (Bm d 1 0)*t1*t2/3
        + 2*(Bm d 1 0)*t2^2/3 + (Bm d 1 1)*t1^2 - 8*(Bm d 1 1)*t1*t2/3 + 4*(Bm d 1 1)*t2^2/3
        + 2*(Bm d 2 0)*t1*t2/3 + 2*(Bm d 2 0)*t2^2/3 - 2*(Bm d 2 1)*t1*t2/3
        + 4*(Bm d 2 1)*t2^2/3)*ks01
    + ((Bm d 0 0)*t1*t2/3 + (Bm d 0 0)*t2^2/3 - (Bm d 0 1)*t1*t2/3 + 2*(Bm d 0 1)*t2^2/3
        - 2*(Bm d 1 0)*t1*t2/3 - 2*(Bm d 1 0)*t2^2/3 + 2*(Bm d 1 1)*t1*t2/3
        - 4*(Bm d 1 1)*t2^2/3 - (Bm d 2 0)*t1^2 - 5*(Bm d 2 0)*t1*t2/3 - 2*(Bm d 2 0)*t2^2/3
        + (Bm d 2 1)*t1^2 - 4*(Bm d 2 1)*t1*t2/3 - 4*(Bm d 2 1)*t2^2/3)*ks02
    + (-4*(Bm d 0 0)*t1*t2/3 - 4*(Bm d 0 0)*t2^2/3 + 4*(Bm d 0 1)*t1*t2/3
        - 8*(Bm d 0 1)*t2^2/3 - (Bm d 1 0)*t1*t2/3 - (Bm d 1 0)*t2^2/3 + (Bm d 1 1)*t1*t2/3
        - 2*(Bm d 1 1)*t2^2/3 + (Bm d 2 0)*t1^2 + 2*(Bm d 2 0)*t1*t2/3 - (Bm d 2 0)*t2^2/3
        - (Bm d 2 1)*t1^2 + 7*(Bm d 2 1)*t1*t2/3 - 2*(Bm d 2 1)*t2^2/3)*ks12


/-! ### Discharging `θ ≥ 1/2` and `Δ ≥ 0` in the rank-two case -/

/-- The quotient `M`-form is positive semidefinite, since `M ⪰ 0` on all of `ℝ³`. -/
lemma Qform_quotient_psd (t1 t2 : ℝ) :
    0 ≤ Qform (kb11 d) (kb12 d) (kb22 d) (xb11 d) (xb12 d) (xb21 d) (xb22 d) t1 t2 := by
  rw [← Mform_quotient d t1 t2]
  exact d.hMpsd (fun i => t1 * f1 i + t2 * f2 i)

/-- `x₁₂ = 0` case of the determinant bound: then `det X = x₁₁x₂₂`, and testing `Q` at the two
coordinate directions gives `k₁₁x₁₁ ≥ 0` and `k₂₂x₂₂ ≥ 0`; positive definiteness of `K` makes
`k₁₁, k₂₂ > 0`, so both diagonal entries are nonnegative. -/
lemma det_nonneg_accretive_diag
    (k11 k12 k22 x11 x12 x21 x22 : ℝ)
    (hx12 : x12 = 0)
    (hKpd : ∀ w1 w2 : ℝ, (w1 ≠ 0 ∨ w2 ≠ 0) → 0 < k11*w1^2 + 2*k12*w1*w2 + k22*w2^2)
    (hQ : ∀ v1 v2 : ℝ, 0 ≤ Qform k11 k12 k22 x11 x12 x21 x22 v1 v2) :
    0 ≤ x11*x22 - x12*x21 := by
  have hk11 : 0 < k11 := by
    have := hKpd 1 0 (Or.inl one_ne_zero); nlinarith [this]
  have hk22 : 0 < k22 := by
    have := hKpd 0 1 (Or.inr one_ne_zero); nlinarith [this]
  -- Q(1,0) = 2(k₁₁x₁₁ + k₁₂x₂₁) and Q(0,1) = 2(k₁₂x₁₂ + k₂₂x₂₂) = 2k₂₂x₂₂ when x₁₂ = 0
  have h2 : 0 ≤ 2*(k12*x12 + k22*x22) := by
    have := hQ 0 1; unfold Qform at this; nlinarith [this]
  have hx22 : 0 ≤ x22 := by rw [hx12] at h2; nlinarith [h2, hk22]
  -- for x₁₁: if x₁₁ < 0 then λ = x₁₁ is a negative eigenvalue with eigenvector (1,0)
  -- (since x₁₂ = 0, the first coordinate axis is X-invariant)
  rcases le_or_gt 0 x11 with hx11 | hx11
  · rw [hx12]; nlinarith [mul_nonneg hx11 hx22]
  · exfalso
    -- with `x₁₂ = 0` the matrix is lower triangular; `λ = x₁₁ < 0` is an eigenvalue with
    -- right eigenvector `(x₁₁ − x₂₂, x₂₁)`, which is nonzero because `x₁₁ < 0 ≤ x₂₂`.
    have hne : x11 - x22 ≠ 0 := by intro hc; nlinarith [hx11, hx22]
    have he1 : x11*(x11 - x22) + x12*x21 = x11*(x11 - x22) := by rw [hx12]; ring
    have he2 : x21*(x11 - x22) + x22*x21 = x11*x21 := by ring
    have hKv := hKpd (x11 - x22) x21 (Or.inl hne)
    have := det_nonneg_of_accretive k11 k12 k22 x11 x12 x21 x22 x11 (x11 - x22) x21
      hKv hx11 he1 he2
    linarith [hQ (x11 - x22) x21, this]

/-- **`Δ = σ₂(B) ≥ 0` in the rank-two case, unconditionally.**  This is the hypothesis
`hDelta` that `trichotomy_input` and `theta_one_impossible` previously assumed. -/
lemma sig2B_nonneg (hdet : 0 < kb11 d * kb22 d - (kb12 d) ^ 2) : 0 ≤ sig2B d := by
  rw [← det_xb d]
  rcases eq_or_ne (xb12 d) 0 with h | h
  · exact det_nonneg_accretive_diag _ _ _ _ _ _ _ h (Kb_pd_of_rank_two d hdet)
      (Qform_quotient_psd d)
  · exact det_nonneg_accretive_generic _ _ _ _ _ _ _ h (Kb_pd_of_rank_two d hdet)
      (Qform_quotient_psd d)

/-- **`θ ≥ 1/2` in the rank-two case, unconditionally.**  This is the hypothesis `htau`
that `trichotomy_input` previously assumed. -/
lemma theta_ge_half (hdet : 0 < kb11 d * kb22 d - (kb12 d) ^ 2) : 1/2 ≤ theta d := by
  have hk22 : 0 < kb22 d := by
    have := Kb_pd_of_rank_two d hdet 0 1 (Or.inr one_ne_zero); nlinarith [this]
  have h := trace_nonneg_accretive (kb11 d) (kb12 d) (kb22 d)
    (xb11 d) (xb12 d) (xb21 d) (xb22 d) hk22 hdet (Qform_quotient_psd d)
  rw [trace_xb d] at h
  linarith


/-! ### The trichotomy, with no assumed hypotheses (rank-two case)

With `sig2B_nonneg` and `theta_ge_half` in hand, the `Δ ≥ 0` and `θ ≥ 1/2` inputs to the
trichotomy are theorems rather than assumptions, and the `θ = 1` branch closes outright. -/

/-- **The trichotomy in the rank-two case**, with both former hypotheses discharged:
either `θ = 1/2` or `θ ≥ 1`. -/
lemma trichotomy_rank_two (hdet : 0 < kb11 d * kb22 d - (kb12 d) ^ 2) :
    theta d = 1/2 ∨ 1 ≤ theta d :=
  trichotomy_input d (theta_ge_half d hdet) (sig2B_nonneg d hdet)

/-- **`θ = 1` is impossible in the rank-two case**, unconditionally. -/
theorem theta_one_impossible_rank_two (hdet : 0 < kb11 d * kb22 d - (kb12 d) ^ 2)
    (hth : theta d = 1) : False :=
  theta_one_impossible d hth (sig2B_nonneg d hdet)


/-! ### The rank-one normal form

In the rank-one case `det K̄ = 0`, and positive semidefiniteness plus `K̄ ≠ 0` put `K̄` in the
normal form `K̄ = w wᵗ` for an explicit `w`.  Then `K̄ B̄ = w (B̄ᵗw)ᵗ`, so with `u = B̄ᵗ w` the
descended form is `Q = w uᵗ + u wᵗ`, whose determinant is `−(u₁w₂ − u₂w₁)²`.  Semidefiniteness
forces that determinant to be `≥ 0`, hence `u ∥ w`, and testing `Q` at `w` gives `λ ≥ 0`. -/

/-- A positive semidefinite `2 × 2` form has nonnegative determinant.  Elementary: if
`ac − b² < 0` then the form is negative at `(b, −a)` when `a > 0`, at `(−c, b)` when `c > 0`,
and at `(1, ±1)` when `a = c = 0` (then `b ≠ 0`). -/
lemma psd_det_nonneg (a b c : ℝ)
    (h : ∀ v1 v2 : ℝ, 0 ≤ a*v1^2 + 2*b*v1*v2 + c*v2^2) :
    0 ≤ a*c - b^2 := by
  have ha : 0 ≤ a := by have := h 1 0; nlinarith [this]
  have hc : 0 ≤ c := by have := h 0 1; nlinarith [this]
  by_contra hneg
  have hlt : a*c - b^2 < 0 := by linarith
  rcases lt_or_eq_of_le ha with hapos | ha0
  · have := h b (-a); nlinarith [this, hapos, hlt]
  · -- a = 0, so b² > 0
    rcases lt_or_eq_of_le hc with hcpos | hc0
    · have := h (-c) b; nlinarith [this, hcpos, hlt]
    · -- a = c = 0 and b ≠ 0: the form is 2b·v₁v₂, negative in one of the two diagonals
      have hb : b ≠ 0 := by intro hb0; rw [hb0] at hlt; nlinarith [hlt, ha0.symm, hc0.symm]
      rcases lt_or_gt_of_ne hb with hbneg | hbpos
      · have := h 1 1; nlinarith [this, ha0.symm, hc0.symm, hbneg]
      · have := h 1 (-1); nlinarith [this, ha0.symm, hc0.symm, hbpos]

/-- **The rank-one normal form.**  If the `2 × 2` psd form `K̄` is singular, it is `w wᵗ`:
concretely, `k₁₁ = w₁²`, `k₁₂ = w₁w₂`, `k₂₂ = w₂²` with

  `w = (√k₁₁, k₁₂/√k₁₁)`  when `k₁₁ > 0`,   `w = (0, √k₂₂)`  when `k₁₁ = 0`

(in the second case semidefiniteness already forces `k₁₂ = 0`). -/
lemma rank_one_normal_form (k11 k12 k22 : ℝ)
    (hpsd : ∀ v1 v2 : ℝ, 0 ≤ k11*v1^2 + 2*k12*v1*v2 + k22*v2^2)
    (hsing : k11*k22 - k12^2 = 0) :
    ∃ w1 w2 : ℝ, k11 = w1^2 ∧ k12 = w1*w2 ∧ k22 = w2^2 := by
  have ha : 0 ≤ k11 := by have := hpsd 1 0; nlinarith [this]
  have hc : 0 ≤ k22 := by have := hpsd 0 1; nlinarith [this]
  rcases lt_or_eq_of_le ha with hapos | ha0
  · -- k₁₁ > 0: take w₁ = √k₁₁, w₂ = k₁₂/√k₁₁
    refine ⟨Real.sqrt k11, k12 / Real.sqrt k11, ?_, ?_, ?_⟩
    · exact (Real.sq_sqrt (le_of_lt hapos)).symm
    · have hs : Real.sqrt k11 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hapos)
      field_simp
    · have hs2 : (Real.sqrt k11)^2 = k11 := Real.sq_sqrt (le_of_lt hapos)
      have hs : Real.sqrt k11 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hapos)
      rw [div_pow, hs2]
      field_simp
      linarith [hsing]
  · -- k₁₁ = 0: then k₁₂ = 0, and w = (0, √k₂₂)
    have hk11 : k11 = 0 := ha0.symm
    have hk12 : k12 = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have := hpsd (1/(-k12)) 1
        rw [hk11] at this
        have hlt : k12 * (1/(-k12)) = -1 := by field_simp
        nlinarith [this, hlt]
      · have := hpsd (-(1/k12)) 1
        rw [hk11] at this
        have hlt : k12 * (-(1/k12)) = -1 := by field_simp
        nlinarith [this, hlt]
    exact ⟨0, Real.sqrt k22, by rw [hk11]; ring, by rw [hk12]; ring,
      (Real.sq_sqrt hc).symm⟩

/-- **The eigen-relation.**  If `Q = w uᵗ + u wᵗ` is positive semidefinite and `w ≠ 0`, then
`u = λ w` for some `λ ≥ 0`.  The determinant of `Q` is `−(u₁w₂ − u₂w₁)²`, so semidefiniteness
forces `u ∥ w`; testing `Q` at `w` then gives `2λ(w₁²+w₂²)² ≥ 0`. -/
lemma rank_one_eigen (w1 w2 u1 u2 : ℝ) (hw : w1 ≠ 0 ∨ w2 ≠ 0)
    (hQ : ∀ v1 v2 : ℝ, 0 ≤ 2*(w1*u1)*v1^2 + 2*(w1*u2 + u1*w2)*v1*v2 + 2*(w2*u2)*v2^2) :
    ∃ lam : ℝ, 0 ≤ lam ∧ u1 = lam*w1 ∧ u2 = lam*w2 := by
  -- the determinant of the form, in the normalisation of `psd_det_nonneg`
  have hdet := psd_det_nonneg (2*(w1*u1)) (w1*u2 + u1*w2) (2*(w2*u2)) hQ
  have hpar : u1*w2 - u2*w1 = 0 := by
    have h : -(u1*w2 - u2*w1)^2 = 2*(w1*u1)*(2*(w2*u2)) - (w1*u2 + u1*w2)^2 := by ring
    nlinarith [hdet, h, sq_nonneg (u1*w2 - u2*w1)]
  have hnorm : 0 < w1^2 + w2^2 := by
    rcases hw with h | h
    · positivity
    · positivity
  refine ⟨(u1*w1 + u2*w2)/(w1^2 + w2^2), ?_, ?_, ?_⟩
  · -- λ ≥ 0 from Q(w) = 2(u·w)(w₁²+w₂²) ≥ 0
    have hQw := hQ w1 w2
    have hid : 2*(w1*u1)*w1^2 + 2*(w1*u2 + u1*w2)*w1*w2 + 2*(w2*u2)*w2^2
        = 2*(u1*w1 + u2*w2)*(w1^2 + w2^2) := by ring
    rw [hid] at hQw
    have hmul : 0 ≤ (u1*w1 + u2*w2) * (w1^2 + w2^2) := by linarith
    have : 0 ≤ u1*w1 + u2*w2 := by
      rcases le_or_gt 0 (u1*w1 + u2*w2) with h | h
      · exact h
      · exfalso; nlinarith [hmul, hnorm, h]
    exact div_nonneg this (le_of_lt hnorm)
  · rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hnorm)]
    linear_combination w2 * hpar
  · rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hnorm)]
    linear_combination (-w1) * hpar


/-! ### The rank-one case for the actual data

Assembling: in the rank-one case `det K̄ = 0`, so `K̄ = w wᵗ` by `rank_one_normal_form`; `w ≠ 0`
because `K̄ ≠ 0` (`Kb_ne_zero`); and `Qform (K̄, B̄) = w uᵗ + u wᵗ` for `u = B̄ᵗ w`, so
`rank_one_eigen` produces `λ ≥ 0` with `B̄ᵗ w = λ w`. -/

/-- `Qform` of a rank-one `K̄ = w wᵗ` is exactly the `w uᵗ + u wᵗ` form with `u = B̄ᵗ w`. -/
lemma Qform_rank_one (w1 w2 x11 x12 x21 x22 v1 v2 : ℝ) :
    Qform (w1^2) (w1*w2) (w2^2) x11 x12 x21 x22 v1 v2
      = 2*(w1*(x11*w1 + x21*w2))*v1^2
        + 2*(w1*(x12*w1 + x22*w2) + (x11*w1 + x21*w2)*w2)*v1*v2
        + 2*(w2*(x12*w1 + x22*w2))*v2^2 := by
  unfold Qform; ring

/-- **The rank-one case: `B̄ᵗ` has a nonnegative eigenvalue with eigenvector `w`.**

This is the input the `p`-recursion needs: `λ ≥ 0`, together with `K̄ = w wᵗ` and `w ≠ 0`. -/
theorem rank_one_case (hsing : kb11 d * kb22 d - (kb12 d) ^ 2 = 0) :
    ∃ w1 w2 lam : ℝ, (w1 ≠ 0 ∨ w2 ≠ 0) ∧ 0 ≤ lam ∧
      kb11 d = w1^2 ∧ kb12 d = w1*w2 ∧ kb22 d = w2^2 ∧
      xb11 d * w1 + xb21 d * w2 = lam * w1 ∧
      xb12 d * w1 + xb22 d * w2 = lam * w2 := by
  obtain ⟨w1, w2, h11, h12, h22⟩ :=
    rank_one_normal_form (kb11 d) (kb12 d) (kb22 d) (Kb_psd d) hsing
  -- `w ≠ 0`: otherwise `K̄ = 0`, contradicting `K̄(s₁,s₂) = 1/12`
  have hw : w1 ≠ 0 ∨ w2 ≠ 0 := by
    by_contra hc
    rw [not_or] at hc
    obtain ⟨h1, h2⟩ := hc
    have h1' : w1 = 0 := not_not.mp h1
    have h2' : w2 = 0 := not_not.mp h2
    have hne := Kb_ne_zero d
    rw [h11, h12, h22, h1', h2'] at hne
    norm_num at hne
  -- the descended form, in `w uᵗ + u wᵗ` shape
  have hQ : ∀ v1 v2 : ℝ, 0 ≤ 2*(w1*(xb11 d * w1 + xb21 d * w2))*v1^2
      + 2*(w1*(xb12 d * w1 + xb22 d * w2) + (xb11 d * w1 + xb21 d * w2)*w2)*v1*v2
      + 2*(w2*(xb12 d * w1 + xb22 d * w2))*v2^2 := by
    intro v1 v2
    rw [← Qform_rank_one]
    have h := Qform_quotient_psd d v1 v2
    rw [h11, h12, h22] at h
    exact h
  obtain ⟨lam, hlam, e1, e2⟩ :=
    rank_one_eigen w1 w2 (xb11 d * w1 + xb21 d * w2) (xb12 d * w1 + xb22 d * w2) hw hQ
  exact ⟨w1, w2, lam, hw, hlam, h11, h12, h22, e1, e2⟩


/-! ### Lifting the rank-one data back to `ℝ³`

The quotient vector `w = (w₁, w₂)` lifts to `W ∈ ℝ³` using the basis dual to `(f₁, f₂)` inside
`e^⊥`, namely `g₁ = (2,−1,−1)/3` and `g₂ = (1,1,−2)/3`:

  `W = w₁g₁ + w₂g₂ = ((2w₁+w₂)/3, (w₂−w₁)/3, −(w₁+2w₂)/3)`.

This `W` is forced: a symmetric `K` with `Ke = 0` is determined by the three pairings
`fᵢᵗKfⱼ`, so `fᵢᵗKfⱼ = wᵢwⱼ` for all `i, j` already gives the full matrix identity
`K = W Wᵗ` (`Km_rank_one` below).  Then `Kc = W(Wᵗc) = σW` with `σ = Wᵗc`, and
`σ² = cᵗKc = 1/12`. -/

/-- The lift of the quotient vector `w` to `ℝ³`, landing in `e^⊥`. -/
noncomputable def Wlift (w1 w2 : ℝ) : ℕ → ℝ := fun i =>
  if i = 0 then (2*w1 + w2)/3 else if i = 1 then (w2 - w1)/3 else -(w1 + 2*w2)/3

/-- `W` is orthogonal to `e`. -/
lemma Wlift_perp_e (w1 w2 : ℝ) : ∑ i ∈ range 3, Wlift w1 w2 i = 0 := by
  simp only [Wlift, show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num; ring

/-- **`K = W Wᵗ`**, entrywise.  Forced, because a symmetric `K` with `Ke = 0` is determined by
the three pairings `fᵢᵗKfⱼ`, which are `wᵢwⱼ` in the rank-one case. -/
lemma Km_rank_one (w1 w2 : ℝ)
    (h11 : kb11 d = w1^2) (h12 : kb12 d = w1*w2) (h22 : kb22 d = w2^2)
    (i j : ℕ) (hi : i ∈ range 3) (hj : j ∈ range 3) :
    Km d i j = Wlift w1 w2 i * Wlift w1 w2 j := by
  have ke0 := Km_e d 0 (by simp)
  have ke1 := Km_e d 1 (by simp)
  have ke2 := Km_e d 2 (by simp)
  have ks01 : Km d 0 1 = Km d 1 0 := by
    simp only [Km]; rw [d.hRsymm 0 (by simp) 1 (by simp)]; ring
  have ks02 : Km d 0 2 = Km d 2 0 := by
    simp only [Km]; rw [d.hRsymm 0 (by simp) 2 (by simp)]; ring
  have ks12 : Km d 1 2 = Km d 2 1 := by
    simp only [Km]; rw [d.hRsymm 1 (by simp) 2 (by simp)]; ring
  simp only [kb11, kb12, kb22, Kpair, f1, f2,
    show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at h11 h12 h22
  norm_num at h11 h12 h22
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at ke0 ke1 ke2
  have hi' := mem_range.1 hi; have hj' := mem_range.1 hj
  interval_cases i <;> interval_cases j <;> simp only [Wlift] <;> norm_num
  case _ => linear_combination (4/9)*h11 + (4/9)*h12 + (1/9)*h22 + (5/9)*ke0 + (-1/9)*ke1 + (-1/9)*ke2 + (-5/9)*ks01 + (-1/9)*ks02 + (-2/9)*ks12
  case _ => linear_combination (-2/9)*h11 + (1/9)*h12 + (1/9)*h22 + (2/9)*ke0 + (2/9)*ke1 + (-1/9)*ke2 + (4/9)*ks01 + (-1/9)*ks02 + (-2/9)*ks12
  case _ => linear_combination (-2/9)*h11 + (-5/9)*h12 + (-2/9)*h22 + (2/9)*ke0 + (-1/9)*ke1 + (2/9)*ke2 + (1/9)*ks01 + (2/9)*ks02 + (4/9)*ks12
  case _ => linear_combination (-2/9)*h11 + (1/9)*h12 + (1/9)*h22 + (2/9)*ke0 + (2/9)*ke1 + (-1/9)*ke2 + (-5/9)*ks01 + (-1/9)*ks02 + (-2/9)*ks12
  case _ => linear_combination (1/9)*h11 + (-2/9)*h12 + (1/9)*h22 + (-1/9)*ke0 + (5/9)*ke1 + (-1/9)*ke2 + (4/9)*ks01 + (-1/9)*ks02 + (-2/9)*ks12
  case _ => linear_combination (1/9)*h11 + (1/9)*h12 + (-2/9)*h22 + (-1/9)*ke0 + (2/9)*ke1 + (2/9)*ke2 + (1/9)*ks01 + (2/9)*ks02 + (4/9)*ks12
  case _ => linear_combination (-2/9)*h11 + (-5/9)*h12 + (-2/9)*h22 + (2/9)*ke0 + (-1/9)*ke1 + (2/9)*ke2 + (1/9)*ks01 + (-7/9)*ks02 + (4/9)*ks12
  case _ => linear_combination (1/9)*h11 + (1/9)*h12 + (-2/9)*h22 + (-1/9)*ke0 + (2/9)*ke1 + (2/9)*ke2 + (1/9)*ks01 + (2/9)*ks02 + (-5/9)*ks12
  case _ => linear_combination (1/9)*h11 + (4/9)*h12 + (4/9)*h22 + (-1/9)*ke0 + (-1/9)*ke1 + (5/9)*ke2 + (-2/9)*ks01 + (5/9)*ks02 + (1/9)*ks12


/-- **`Aᵗb = ½b − Kc`, coordinatewise** (equation `ATb-general` of the note).  A rearrangement
of `Rc_eq` using `R = K + bbᵗ` and `bᵗc = 1/2`. -/
lemma ATb_eq (j : ℕ) (hj : j ∈ range 3) :
    ∑ i ∈ range 3, d.A i j * d.b i
      = d.b j / 2 - ∑ k ∈ range 3, Km d j k * d.c k := by
  have rc := Rc_eq d j hj
  have h2 := d.h2
  rw [sum3] at h2
  simp only [Km, show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at rc ⊢
  linear_combination rc - d.b j * h2

/-- `σ := Wᵗc`. -/
noncomputable def sigma_of (w1 w2 : ℝ) : ℝ := ∑ i ∈ range 3, Wlift w1 w2 i * d.c i

/-- **`Kc = σW`, coordinatewise.**  Immediate from `K = W Wᵗ`. -/
lemma Kc_eq_sigma_W (w1 w2 : ℝ)
    (h11 : kb11 d = w1^2) (h12 : kb12 d = w1*w2) (h22 : kb22 d = w2^2)
    (j : ℕ) (hj : j ∈ range 3) :
    ∑ k ∈ range 3, Km d j k * d.c k = sigma_of d w1 w2 * Wlift w1 w2 j := by
  have hK : ∀ k ∈ range 3, Km d j k = Wlift w1 w2 j * Wlift w1 w2 k :=
    fun k hk => Km_rank_one d w1 w2 h11 h12 h22 j k hj hk
  rw [Finset.sum_congr rfl (fun k hk => by rw [hK k hk])]
  simp only [sigma_of, show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

/-- **`σ² = 1/12`.**  Because `σ² = cᵗ(WWᵗ)c = cᵗKc = 1/12`. -/
lemma sigma_sq (w1 w2 : ℝ)
    (h11 : kb11 d = w1^2) (h12 : kb12 d = w1*w2) (h22 : kb22 d = w2^2) :
    (sigma_of d w1 w2)^2 = 1/12 := by
  have hc := cKc d
  have hK : ∀ i ∈ range 3, ∀ j ∈ range 3,
      Km d i j = Wlift w1 w2 i * Wlift w1 w2 j :=
    fun i hi j hj => Km_rank_one d w1 w2 h11 h12 h22 i j hi hj
  have k00 := hK 0 (by simp) 0 (by simp); have k01 := hK 0 (by simp) 1 (by simp)
  have k02 := hK 0 (by simp) 2 (by simp); have k10 := hK 1 (by simp) 0 (by simp)
  have k11' := hK 1 (by simp) 1 (by simp); have k12' := hK 1 (by simp) 2 (by simp)
  have k20 := hK 2 (by simp) 0 (by simp); have k21 := hK 2 (by simp) 1 (by simp)
  have k22' := hK 2 (by simp) 2 (by simp)
  simp only [Km] at k00 k01 k02 k10 k11' k12' k20 k21 k22'
  simp only [sigma_of, show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero] at hc ⊢
  linear_combination hc - d.c 0 * d.c 0 * k00 - d.c 0 * d.c 1 * k01
    - d.c 0 * d.c 2 * k02 - d.c 1 * d.c 0 * k10 - d.c 1 * d.c 1 * k11'
    - d.c 1 * d.c 2 * k12' - d.c 2 * d.c 0 * k20 - d.c 2 * d.c 1 * k21
    - d.c 2 * d.c 2 * k22'

/-- **The lifted eigen-relation `BᵗW = λW`, coordinatewise.** -/
lemma BtW_eq (w1 w2 lam : ℝ)
    (e1 : xb11 d * w1 + xb21 d * w2 = lam * w1)
    (e2 : xb12 d * w1 + xb22 d * w2 = lam * w2)
    (j : ℕ) (hj : j ∈ range 3) :
    ∑ i ∈ range 3, Bm d i j * Wlift w1 w2 i = lam * Wlift w1 w2 j := by
  have be0 := Bm_e d 0 (by simp)
  have be1 := Bm_e d 1 (by simp)
  have be2 := Bm_e d 2 (by simp)
  simp only [xb11, xb12, xb21, xb22] at e1 e2
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero] at be0 be1 be2 ⊢
  have hj' := mem_range.1 hj
  interval_cases j <;> simp only [Wlift] <;> norm_num
  case _ => linear_combination (2/3)*e1 + (1/3)*e2
  case _ => linear_combination (-1/3)*e1 + (1/3)*e2
  case _ => linear_combination (-1/3)*e1 + (-2/3)*e2
    + (2*w1/3 + w2/3)*be0 + (-w1/3 + w2/3)*be1 + (-w1/3 - 2*w2/3)*be2

/-- **`WᵗA = λWᵗ + σbᵗ`, coordinatewise** (equation `eigrel` of the note).  Since
`B = A − cbᵗ`, the relation `BᵗW = λW` reads `AᵗW − b(cᵗW) = λW`, and `cᵗW = σ`. -/
lemma WtA_eq (w1 w2 lam : ℝ)
    (e1 : xb11 d * w1 + xb21 d * w2 = lam * w1)
    (e2 : xb12 d * w1 + xb22 d * w2 = lam * w2)
    (j : ℕ) (hj : j ∈ range 3) :
    ∑ i ∈ range 3, Wlift w1 w2 i * d.A i j
      = lam * Wlift w1 w2 j + sigma_of d w1 w2 * d.b j := by
  have h := BtW_eq d w1 w2 lam e1 e2 j hj
  simp only [Bm, sigma_of, show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero] at h ⊢
  linear_combination h


/-! ### The `p`/`q` recursion, and the rank-one contradiction

Set `Aᵏc` by iteration, `pₖ = bᵗAᵏc`, `qₖ = WᵗAᵏc`.  One application of `Aᵗb = ½b − Kc` and
`Kc = σW` gives `pₖ₊₁ = ½pₖ − σqₖ`; one application of `WᵗA = λWᵗ + σbᵗ` gives
`qₖ₊₁ = σpₖ + λqₖ`.  Writing `qₖ = σrₖ` (legitimate since `σ² = 1/12` makes `σ ≠ 0`) and using
`σ² = 1/12` turns these into the rational recursion of `rank_one_recursion`, whose fifth
iterate is negative — contradicting `pₖ = bᵗAᵏc ≥ 0`. -/

/-- The iterates `Aᵏc`. -/
noncomputable def Ait : ℕ → ℕ → ℝ
  | 0 => d.c
  | (k+1) => fun i => ∑ j ∈ range 3, d.A i j * Ait k j

/-- `Aᵏc ≥ 0`, since `A ≥ 0` and `c = Ae ≥ 0`. -/
lemma Ait_nonneg (k : ℕ) (i : ℕ) (hi : i ∈ range 3) : 0 ≤ Ait d k i := by
  induction k generalizing i with
  | zero => exact c_nonneg d i hi
  | succ n ih =>
    refine Finset.sum_nonneg fun j hj => mul_nonneg (d.hA i hi j hj) (ih j hj)

/-- `pₖ := bᵗAᵏc`. -/
noncomputable def pk (k : ℕ) : ℝ := ∑ i ∈ range 3, d.b i * Ait d k i

/-- `qₖ := WᵗAᵏc`. -/
noncomputable def qk (w1 w2 : ℝ) (k : ℕ) : ℝ := ∑ i ∈ range 3, Wlift w1 w2 i * Ait d k i

/-- **`pₖ ≥ 0`**, from `b ≥ 0` and `Aᵏc ≥ 0`. -/
lemma pk_nonneg (k : ℕ) : 0 ≤ pk d k :=
  Finset.sum_nonneg fun i hi => mul_nonneg (d.hbnn i hi) (Ait_nonneg d k i hi)

/-- `p₀ = bᵗc = 1/2`. -/
lemma pk_zero : pk d 0 = 1/2 := by
  have h2 := d.h2
  simp only [pk, Ait]
  exact h2

/-- `q₀ = Wᵗc = σ`. -/
lemma qk_zero (w1 w2 : ℝ) : qk d w1 w2 0 = sigma_of d w1 w2 := by
  simp only [qk, Ait, sigma_of]

/-- **`pₖ₊₁ = ½pₖ − σqₖ`.**  Move `A` onto `b` with `Aᵗb = ½b − Kc`, then `Kc = σW`. -/
lemma pk_succ (w1 w2 : ℝ)
    (h11 : kb11 d = w1^2) (h12 : kb12 d = w1*w2) (h22 : kb22 d = w2^2) (k : ℕ) :
    pk d (k+1) = 1/2 * pk d k - sigma_of d w1 w2 * qk d w1 w2 k := by
  have hswap : pk d (k+1) = ∑ j ∈ range 3, (∑ i ∈ range 3, d.A i j * d.b i) * Ait d k j := by
    simp only [pk, Ait, show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
      Finset.sum_range_zero]
    ring
  have hAT : ∀ j ∈ range 3, (∑ i ∈ range 3, d.A i j * d.b i)
      = d.b j / 2 - sigma_of d w1 w2 * Wlift w1 w2 j := fun j hj => by
    rw [ATb_eq d j hj, Kc_eq_sigma_W d w1 w2 h11 h12 h22 j hj]
  rw [hswap, Finset.sum_congr rfl (fun j hj => by rw [hAT j hj])]
  simp only [pk, qk, show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

/-- **`qₖ₊₁ = σpₖ + λqₖ`.**  One application of `WᵗA = λWᵗ + σbᵗ`. -/
lemma qk_succ (w1 w2 lam : ℝ)
    (e1 : xb11 d * w1 + xb21 d * w2 = lam * w1)
    (e2 : xb12 d * w1 + xb22 d * w2 = lam * w2) (k : ℕ) :
    qk d w1 w2 (k+1) = sigma_of d w1 w2 * pk d k + lam * qk d w1 w2 k := by
  have hswap : qk d w1 w2 (k+1)
      = ∑ j ∈ range 3, (∑ i ∈ range 3, Wlift w1 w2 i * d.A i j) * Ait d k j := by
    simp only [qk, Ait, show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
      Finset.sum_range_zero]
    ring
  have hW : ∀ j ∈ range 3, (∑ i ∈ range 3, Wlift w1 w2 i * d.A i j)
      = lam * Wlift w1 w2 j + sigma_of d w1 w2 * d.b j :=
    fun j hj => WtA_eq d w1 w2 lam e1 e2 j hj
  rw [hswap, Finset.sum_congr rfl (fun j hj => by rw [hW j hj])]
  simp only [pk, qk, show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring


/-- **Rank one is impossible** (Proposition `rank1` of the note).

With `rₖ := qₖ/σ` the two recursions become `pₖ₊₁ = ½pₖ − (1/12)rₖ` and `rₖ₊₁ = pₖ + λrₖ`
(using `σ² = 1/12`), with `p₀ = 1/2` and `r₀ = 1`.  Then `rank_one_recursion` gives `p₅ < 0`,
contradicting `pk_nonneg`. -/
theorem rank_one_impossible (hsing : kb11 d * kb22 d - (kb12 d) ^ 2 = 0) : False := by
  obtain ⟨w1, w2, lam, hw, hlam, h11, h12, h22, e1, e2⟩ := rank_one_case d hsing
  set sg : ℝ := sigma_of d w1 w2 with hsg
  have hsg2 : sg^2 = 1/12 := sigma_sq d w1 w2 h11 h12 h22
  have hsgne : sg ≠ 0 := by
    intro hc; rw [hc] at hsg2; norm_num at hsg2
  -- the two recursions
  have hp : ∀ k, pk d (k+1) = 1/2 * pk d k - sg * qk d w1 w2 k :=
    fun k => pk_succ d w1 w2 h11 h12 h22 k
  have hq : ∀ k, qk d w1 w2 (k+1) = sg * pk d k + lam * qk d w1 w2 k :=
    fun k => qk_succ d w1 w2 lam e1 e2 k
  -- `rₖ := 12·σ·qₖ`.  Since `σ² = 1/12` this is the same as `qₖ/σ`, but stated with a
  -- multiplication so that no denominators ever appear.
  set r : ℕ → ℝ := fun k => 12 * sg * qk d w1 w2 k with hr
  have hr0 : r 0 = 1 := by
    simp only [hr, qk_zero d w1 w2, ← hsg]
    linear_combination 12 * hsg2
  have hrsucc : ∀ k, r (k+1) = pk d k + lam * r k := by
    intro k
    simp only [hr]
    rw [hq k]
    linear_combination 12 * pk d k * hsg2
  -- `pₖ₊₁ = ½pₖ − (1/12)rₖ`, since `σ·qₖ = rₖ/12` by definition
  have hpsucc : ∀ k, pk d (k+1) = 1/2 * pk d k - 1/12 * r k := by
    intro k
    rw [hp k]
    simp only [hr]
    ring
  -- feed the five steps to `rank_one_recursion`
  have hp5 : pk d 5 < 0 :=
    rank_one_recursion lam (pk d 0) (pk d 1) (pk d 2) (pk d 3) (pk d 4) (pk d 5)
      (r 0) (r 1) (r 2) (r 3) (r 4) hlam (pk_zero d) hr0
      (hpsucc 0) (hrsucc 0) (hpsucc 1) (hrsucc 1) (hpsucc 2) (hrsucc 2)
      (hpsucc 3) (hrsucc 3) (hpsucc 4)
  linarith [pk_nonneg d 5, hp5]

/-- **Theorem 1: the general Claim is inconsistent at `s = 3`.**

`rank_dichotomy` splits on `det K̄`.  In the rank-two case (`det K̄ > 0`) the accretivity
lemmas give `θ ≥ 1/2` and `Δ ≥ 0`, so `trichotomy_rank_two` leaves `θ = 1/2` or `θ ≥ 1`;
in the rank-one case (`det K̄ = 0`) `rank_one_impossible` closes outright.

The `θ = 1` sub-case is `theta_one_impossible_rank_two`.  What is still missing is the
`θ = 1/2` and `θ > 1` sub-cases of the rank-two branch. -/
theorem three_stage_rank_one_or_trichotomy :
    (theta d = 1/2 ∨ 1 ≤ theta d) := by
  rcases rank_dichotomy d with hpos | hzero
  · exact trichotomy_rank_two d hpos
  · exact absurd hzero (fun h => (rank_one_impossible d h).elim)


/-! ### The case `θ = 1/2`

At `θ = 1/2` the bound `σ₂(A) ≤ θ²/3 = 1/12` makes `Δ = σ₂(A) − 1/4 + 1/6 ≤ 0`, and `Δ ≥ 0`
forces `Δ = 0`.  Since also `tr B̄ = θ − 1/2 = 0`, Cayley–Hamilton gives `B̄² = 0`.

For the obstruction, take any `u` with `y := B̄u ≠ 0`.  Then `B̄y = B̄²u = 0`, so

  `yᵗQy = 2 yᵗK̄(B̄y) = 0`,

and semidefiniteness upgrades that to `Q y = 0` — but `Qy = K̄B̄y + B̄ᵗK̄y = B̄ᵗK̄y`, and pairing
against `u` gives `uᵗ(B̄ᵗK̄y) = (B̄u)ᵗK̄y = yᵗK̄y > 0` by positive definiteness.  The point worth
noting is that this last identity is trivial — it needs no case analysis of the nilpotent
`B̄`, unlike the `u vᵗ` factorization the note uses. -/

/-- A psd form vanishing at a point has that point in its kernel — the `2 × 2` instance of
`psd_kernel`, in the coordinates used here. -/
lemma psd_kernel2 (a b c y1 y2 : ℝ)
    (hpsd : ∀ v1 v2 : ℝ, 0 ≤ a*v1^2 + 2*b*v1*v2 + c*v2^2)
    (hzero : a*y1^2 + 2*b*y1*y2 + c*y2^2 = 0) :
    a*y1 + b*y2 = 0 ∧ b*y1 + c*y2 = 0 := by
  set M : ℕ → ℕ → ℝ := fun i j => if i = 0 then (if j = 0 then a else b)
    else (if j = 0 then b else c) with hM
  set x : ℕ → ℝ := fun i => if i = 0 then y1 else y2 with hx
  have hsymm : ∀ i ∈ range 2, ∀ j ∈ range 2, M i j = M j i := by
    intro i hi j hj
    have hi' := mem_range.1 hi; have hj' := mem_range.1 hj
    interval_cases i <;> interval_cases j <;> simp only [hM] <;> norm_num
  have hpsd' : ∀ y : ℕ → ℝ, 0 ≤ ∑ i ∈ range 2, ∑ j ∈ range 2, M i j * (y i * y j) := by
    intro y
    have h := hpsd (y 0) (y 1)
    simp only [hM, show (2:ℕ)=1+1 from rfl, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num
    linarith [h]
  have hx0 : ∑ i ∈ range 2, ∑ j ∈ range 2, M i j * (x i * x j) = 0 := by
    simp only [hM, hx, show (2:ℕ)=1+1 from rfl, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num
    linarith [hzero]
  constructor
  · have h := psd_kernel M hsymm hpsd' x hx0 (fun i => if i = 0 then 1 else 0)
    simp only [hM, hx, show (2:ℕ)=1+1 from rfl, Finset.sum_range_succ,
      Finset.sum_range_zero] at h
    norm_num at h
    linarith [h]
  · have h := psd_kernel M hsymm hpsd' x hx0 (fun i => if i = 0 then 0 else 1)
    simp only [hM, hx, show (2:ℕ)=1+1 from rfl, Finset.sum_range_succ,
      Finset.sum_range_zero] at h
    norm_num at h
    linarith [h]

/-- **The nilpotency obstruction, in coordinates.**  If `B̄² = 0` (given as `tr B̄ = 0` and
`det B̄ = 0`), `B̄ ≠ 0`, `K̄` is positive definite and `Q = K̄B̄ + B̄ᵗK̄ ⪰ 0`, then `False`. -/
lemma nilpotent_obstruction_coord
    (k11 k12 k22 x11 x12 x21 x22 : ℝ)
    (htr : x11 + x22 = 0) (hdet : x11*x22 - x12*x21 = 0)
    (hne : x11 ≠ 0 ∨ x12 ≠ 0 ∨ x21 ≠ 0 ∨ x22 ≠ 0)
    (hKpd : ∀ w1 w2 : ℝ, (w1 ≠ 0 ∨ w2 ≠ 0) → 0 < k11*w1^2 + 2*k12*w1*w2 + k22*w2^2)
    (hQ : ∀ v1 v2 : ℝ, 0 ≤ Qform k11 k12 k22 x11 x12 x21 x22 v1 v2) :
    False := by
  -- pick `u` with `B̄u ≠ 0`
  obtain ⟨u1, u2, hy⟩ : ∃ u1 u2 : ℝ, (x11*u1 + x12*u2 ≠ 0 ∨ x21*u1 + x22*u2 ≠ 0) := by
    rcases hne with h | h | h | h
    · exact ⟨1, 0, Or.inl (by simpa using h)⟩
    · exact ⟨0, 1, Or.inl (by simpa using h)⟩
    · exact ⟨1, 0, Or.inr (by simpa using h)⟩
    · exact ⟨0, 1, Or.inr (by simpa using h)⟩
  set y1 : ℝ := x11*u1 + x12*u2 with hy1
  set y2 : ℝ := x21*u1 + x22*u2 with hy2
  -- `B̄y = B̄²u = 0`, by Cayley–Hamilton
  have hBy1 : x11*y1 + x12*y2 = 0 := by
    rw [hy1, hy2]; linear_combination (u1*x11 + u2*x12)*htr - u1*hdet
  have hBy2 : x21*y1 + x22*y2 = 0 := by
    rw [hy1, hy2]; linear_combination (u1*x21 + u2*x22)*htr - u2*hdet
  -- so the `Q`-form vanishes at `y`
  have hQy : Qform k11 k12 k22 x11 x12 x21 x22 y1 y2 = 0 := by
    unfold Qform
    linear_combination (2*(k11*y1 + k12*y2))*hBy1 + (2*(k12*y1 + k22*y2))*hBy2
  -- upgrade to `Qy = 0`
  have hcoef : ∀ v1 v2 : ℝ, Qform k11 k12 k22 x11 x12 x21 x22 v1 v2
      = (2*(k11*x11 + k12*x21))*v1^2
        + 2*(k11*x12 + k12*x22 + k12*x11 + k22*x21)*v1*v2
        + (2*(k12*x12 + k22*x22))*v2^2 := fun v1 v2 => by unfold Qform; ring
  have hQ' : ∀ v1 v2 : ℝ, 0 ≤ (2*(k11*x11 + k12*x21))*v1^2
      + 2*((k11*x12 + k12*x22 + k12*x11 + k22*x21))*v1*v2
      + (2*(k12*x12 + k22*x22))*v2^2 := by
    intro v1 v2; rw [← hcoef v1 v2]; exact hQ v1 v2
  have hQz : (2*(k11*x11 + k12*x21))*y1^2
      + 2*((k11*x12 + k12*x22 + k12*x11 + k22*x21))*y1*y2
      + (2*(k12*x12 + k22*x22))*y2^2 = 0 := by
    rw [← hcoef y1 y2]; exact hQy
  obtain ⟨g1, g2⟩ := psd_kernel2 _ _ _ y1 y2 hQ' hQz
  -- `Qy = B̄ᵗK̄y`; pairing with `u` gives `yᵗK̄y`, which is positive
  have hpair : u1*((2*(k11*x11 + k12*x21))*y1
        + (k11*x12 + k12*x22 + k12*x11 + k22*x21)*y2)
      + u2*((k11*x12 + k12*x22 + k12*x11 + k22*x21)*y1
        + (2*(k12*x12 + k22*x22))*y2) = 0 := by
    linear_combination u1*g1 + u2*g2
  have hyKy : k11*y1^2 + 2*k12*y1*y2 + k22*y2^2 = 0 := by
    rw [hy1, hy2] at hpair ⊢
    linear_combination hpair + (-k11*u1 - k12*u2)*hBy1 + (-k12*u1 - k22*u2)*hBy2
  have := hKpd y1 y2 hy
  linarith


/-! ### The degenerate sub-case `B̄ = 0`

`B̄ = 0` says `B fⱼ ∈ ⟨e⟩` for `j = 1, 2`, and `Be = 0` covers the third basis vector, so
`range B ⊆ ⟨e⟩`, i.e. `B = e fᵗ` — every column of `B` is constant.  Writing `A = cbᵗ + efᵗ`,

  `bᵗAc = (bᵗc)² + (bᵗe)(fᵗc) = 1/4 + fᵗc`,

so `bᵗAc = 1/6` forces `fᵗc = −1/12`.  With `γ := min cᵢ ≥ 0` attained at `i₀`, the vector
`g := f + γb` is nonnegative (from `A_{i₀j} ≥ 0`), and `gᵗe = γ`, `gᵗc = γ/2 − 1/12`.  Then
`g ≥ 0` together with `cⱼ ≥ γ` gives `gᵗc ≥ γ·gᵗe = γ²`, so `γ² − γ/2 + 1/12 ≤ 0` — impossible
by `Bzero_obstruction`. -/

/-- `B̄ = 0` forces every column of `B` to be constant. -/
lemma Bcols_const (h11 : xb11 d = 0) (h12 : xb12 d = 0)
    (h21 : xb21 d = 0) (h22 : xb22 d = 0) (j : ℕ) (hj : j ∈ range 3) :
    Bm d 0 j = Bm d 1 j ∧ Bm d 1 j = Bm d 2 j := by
  have be0 := Bm_e d 0 (by simp)
  have be1 := Bm_e d 1 (by simp)
  have be2 := Bm_e d 2 (by simp)
  simp only [xb11, xb12, xb21, xb22] at h11 h12 h21 h22
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero] at be0 be1 be2
  have hj' := mem_range.1 hj
  interval_cases j
  · exact ⟨by linear_combination (4/3)*h11 + (2/3)*h12 - (2/3)*h21 - (1/3)*h22,
      by linear_combination (-2/3)*h11 - (1/3)*h12 + (4/3)*h21 + (2/3)*h22⟩
  · exact ⟨by linear_combination (-2/3)*h11 + (2/3)*h12 + (1/3)*h21 - (1/3)*h22,
      by linear_combination (1/3)*h11 - (1/3)*h12 - (2/3)*h21 + (2/3)*h22⟩
  · exact ⟨by linear_combination (-2/3)*h11 - (4/3)*h12 + (1/3)*h21 + (2/3)*h22
        + be0 - be1,
      by linear_combination (1/3)*h11 + (2/3)*h12 - (2/3)*h21 - (4/3)*h22
        + be1 - be2⟩

/-- **The case `B̄ = 0` is impossible.** -/
theorem Bbar_zero_impossible (h11 : xb11 d = 0) (h12 : xb12 d = 0)
    (h21 : xb21 d = 0) (h22 : xb22 d = 0) : False := by
  -- `f j := B 0 j`, and every column of `B` equals it
  have hcol : ∀ j ∈ range 3, ∀ i ∈ range 3, Bm d i j = Bm d 0 j := by
    intro j hj i hi
    obtain ⟨e01, e12⟩ := Bcols_const d h11 h12 h21 h22 j hj
    have hi' := mem_range.1 hi
    interval_cases i
    · rfl
    · exact e01.symm
    · rw [← e12, ← e01]
  -- `A i j = c i * b j + f j`
  have hA : ∀ i ∈ range 3, ∀ j ∈ range 3, d.A i j = d.c i * d.b j + Bm d 0 j := by
    intro i hi j hj
    have h := hcol j hj i hi
    simp only [Bm] at h ⊢
    linarith
  -- `fᵗe = 0` (this is `Be = 0` for row 0)
  have hfe : Bm d 0 0 + Bm d 0 1 + Bm d 0 2 = 0 := by
    have h := Bm_e d 0 (by simp)
    simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
      Finset.sum_range_zero] at h
    linarith
  -- `bᵗAc = 1/4 + fᵗc`, so `fᵗc = −1/12`
  have h1 := d.h1; have h2 := d.h2; have h4 := d.h4
  rw [sum3] at h1 h2
  have hfc : Bm d 0 0 * d.c 0 + Bm d 0 1 * d.c 1 + Bm d 0 2 * d.c 2 = -(1/12) := by
    simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
      Finset.sum_range_zero] at h4
    have a00 := hA 0 (by simp) 0 (by simp); have a01 := hA 0 (by simp) 1 (by simp)
    have a02 := hA 0 (by simp) 2 (by simp); have a10 := hA 1 (by simp) 0 (by simp)
    have a11 := hA 1 (by simp) 1 (by simp); have a12 := hA 1 (by simp) 2 (by simp)
    have a20 := hA 2 (by simp) 0 (by simp); have a21 := hA 2 (by simp) 1 (by simp)
    have a22 := hA 2 (by simp) 2 (by simp)
    rw [a00, a01, a02, a10, a11, a12, a20, a21, a22] at h4
    nlinarith [h4, h1, h2]
  -- `γ := min cᵢ`, attained at some index `i₀`
  have hc0 := c_nonneg d 0 (by simp)
  have hc1 := c_nonneg d 1 (by simp)
  have hc2 := c_nonneg d 2 (by simp)
  obtain ⟨i0, hi0, hmin⟩ : ∃ i0 ∈ range 3, ∀ j ∈ range 3, d.c i0 ≤ d.c j := by
    rcases le_total (d.c 0) (d.c 1) with h01 | h01
    · rcases le_total (d.c 0) (d.c 2) with h02 | h02
      · exact ⟨0, by simp, fun j hj => by
          have hj' := mem_range.1 hj; interval_cases j <;> linarith⟩
      · exact ⟨2, by simp, fun j hj => by
          have hj' := mem_range.1 hj; interval_cases j <;> linarith⟩
    · rcases le_total (d.c 1) (d.c 2) with h12' | h12'
      · exact ⟨1, by simp, fun j hj => by
          have hj' := mem_range.1 hj; interval_cases j <;> linarith⟩
      · exact ⟨2, by simp, fun j hj => by
          have hj' := mem_range.1 hj; interval_cases j <;> linarith⟩
  set gam : ℝ := d.c i0 with hgam
  have hmin' : ∀ j ∈ range 3, gam ≤ d.c j := fun j hj => hmin j hj
  have hgam0 : 0 ≤ gam := c_nonneg d i0 hi0
  -- `g j := f j + γ b j ≥ 0`, from `A i₀ j ≥ 0`
  have hgnn : ∀ j ∈ range 3, 0 ≤ Bm d 0 j + gam * d.b j := by
    intro j hj
    have hAij := d.hA i0 hi0 j hj
    rw [hA i0 hi0 j hj] at hAij
    linarith
  -- `gᵗc ≥ γ·gᵗe = γ²`
  have hge : (Bm d 0 0 + gam * d.b 0) + (Bm d 0 1 + gam * d.b 1)
      + (Bm d 0 2 + gam * d.b 2) = gam := by
    linear_combination hfe + gam * h1
  have hgc : (Bm d 0 0 + gam * d.b 0) * d.c 0 + (Bm d 0 1 + gam * d.b 1) * d.c 1
      + (Bm d 0 2 + gam * d.b 2) * d.c 2 = gam/2 - 1/12 := by
    linear_combination hfc + gam * h2
  have hbound : gam * gam ≤ gam/2 - 1/12 := by
    have m0 := hmin' 0 (by simp); have m1 := hmin' 1 (by simp)
    have m2 := hmin' 2 (by simp)
    have g0 := hgnn 0 (by simp); have g1 := hgnn 1 (by simp); have g2 := hgnn 2 (by simp)
    rw [← hgc]
    have t0 : (Bm d 0 0 + gam * d.b 0) * gam ≤ (Bm d 0 0 + gam * d.b 0) * d.c 0 :=
      mul_le_mul_of_nonneg_left m0 g0
    have t1 : (Bm d 0 1 + gam * d.b 1) * gam ≤ (Bm d 0 1 + gam * d.b 1) * d.c 1 :=
      mul_le_mul_of_nonneg_left m1 g1
    have t2 : (Bm d 0 2 + gam * d.b 2) * gam ≤ (Bm d 0 2 + gam * d.b 2) * d.c 2 :=
      mul_le_mul_of_nonneg_left m2 g2
    have hexp : (Bm d 0 0 + gam * d.b 0) * gam + (Bm d 0 1 + gam * d.b 1) * gam
        + (Bm d 0 2 + gam * d.b 2) * gam = gam * gam := by
      linear_combination gam * hge
    linarith [t0, t1, t2, hexp]
  exact Bzero_obstruction gam (by nlinarith [hbound])


/-- **`θ = 1/2` is impossible in the rank-two case.**

`sig2A_le` gives `σ₂(A) ≤ θ²/3 = 1/12`, so `Δ = σ₂(A) − θ/2 + 1/6 ≤ 0`; with `Δ ≥ 0` from
`sig2B_nonneg` this pins `Δ = 0`.  Since `tr B̄ = θ − 1/2 = 0` as well, `B̄` is nilpotent, and
`nilpotent_obstruction_coord` closes the case when `B̄ ≠ 0`, `Bbar_zero_impossible` when
`B̄ = 0`. -/
theorem theta_half_impossible (hdet : 0 < kb11 d * kb22 d - (kb12 d) ^ 2)
    (hth : theta d = 1/2) : False := by
  -- `Δ = 0`
  have hD := Delta_id d
  have hle := sig2A_le d
  have hDnn := sig2B_nonneg d hdet
  have hDzero : sig2B d = 0 := by
    rw [hth] at hD hle
    norm_num at hD hle
    linarith
  -- `tr B̄ = 0` and `det B̄ = 0`
  have htr : xb11 d + xb22 d = 0 := by rw [trace_xb d, hth]; ring
  have hdt : xb11 d * xb22 d - xb12 d * xb21 d = 0 := by rw [det_xb d]; exact hDzero
  -- split on whether `B̄` vanishes
  by_cases hz : xb11 d = 0 ∧ xb12 d = 0 ∧ xb21 d = 0 ∧ xb22 d = 0
  · exact Bbar_zero_impossible d hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  · refine nilpotent_obstruction_coord (kb11 d) (kb12 d) (kb22 d)
      (xb11 d) (xb12 d) (xb21 d) (xb22 d) htr hdt ?_
      (Kb_pd_of_rank_two d hdet) (Qform_quotient_psd d)
    by_contra hc
    rw [not_or, not_or, not_or] at hc
    exact hz ⟨not_not.mp hc.1, not_not.mp hc.2.1, not_not.mp hc.2.2.1,
      not_not.mp hc.2.2.2⟩


/-! ### The case `θ > 1`

The sharpened diagonal bound weights each off-diagonal entry of row `i` by `bᵢmᵢ` rather than
`0`, where `mᵢ = min_{j≠i} cⱼ`:

  `Σᵢ bᵢ[cᵢdᵢ + (cᵢ − dᵢ)mᵢ] ≤ bᵗAc = 1/6`.

Under the ordering `c₀ ≤ c₁ ≤ c₂` the left side rearranges, using `bᵗc = 1/2`, to

  `c₀/2 + b₀(c₁−c₀)(c₀−d₀) + β₁d₁ + β₂d₂`   with `β₁ = b₁(c₁−c₀)`, `β₂ = b₂(c₂−c₀)`,

and `d₀ ≤ c₀` makes the middle term nonnegative.  Dropping it and using
`β₁ + β₂ = 1/2 − c₀` gives `min(d₁,d₂) ≤ g(c₀) := (1/3−c₀)/(1−2c₀)`, hence
`v = m(u−m) ≤ g(u−g)`.  Against the lower bound `v ≥ (c₀+u)/2 − 1/6 − c₀u` coming from
`Δ ≥ 0`, that contradicts `rank_two_key`. -/

/-- **The sharpened diagonal bound** (Lemma `sharp`), under the ordering `c₀ ≤ c₁ ≤ c₂`. -/
lemma sharp_bound (h01 : d.c 0 ≤ d.c 1) (h12 : d.c 1 ≤ d.c 2) :
    d.c 0 / 2 + d.b 0 * (d.c 1 - d.c 0) * (d.c 0 - d.A 0 0)
      + d.b 1 * (d.c 1 - d.c 0) * d.A 1 1 + d.b 2 * (d.c 2 - d.c 0) * d.A 2 2 ≤ 1/6 := by
  have h4 := d.h4
  have h2 := d.h2
  rw [sum3] at h2
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero] at h4
  -- every off-diagonal entry of row `i` is weighted by `cⱼ ≥ mᵢ`
  have b0 := d.hbnn 0 (by simp); have b1 := d.hbnn 1 (by simp); have b2 := d.hbnn 2 (by simp)
  have a01 := d.hA 0 (by simp) 1 (by simp); have a02 := d.hA 0 (by simp) 2 (by simp)
  have a10 := d.hA 1 (by simp) 0 (by simp); have a12 := d.hA 1 (by simp) 2 (by simp)
  have a20 := d.hA 2 (by simp) 0 (by simp); have a21 := d.hA 2 (by simp) 1 (by simp)
  -- the three off-diagonal slack terms, each nonnegative
  have s1 : 0 ≤ d.b 0 * d.A 0 2 * (d.c 2 - d.c 1) :=
    mul_nonneg (mul_nonneg b0 a02) (by linarith)
  have s2 : 0 ≤ d.b 1 * d.A 1 2 * (d.c 2 - d.c 0) :=
    mul_nonneg (mul_nonneg b1 a12) (by linarith)
  have s3 : 0 ≤ d.b 2 * d.A 2 1 * (d.c 1 - d.c 0) :=
    mul_nonneg (mul_nonneg b2 a21) (by linarith)
  -- the row sums `cᵢ = Σⱼ aᵢⱼ`
  have c0 := d.hc 0 (by simp); have c1 := d.hc 1 (by simp); have c2 := d.hc 2 (by simp)
  rw [sum3] at c0 c1 c2
  -- exact identity: `bᵗAc − LHS = s₁ + s₂ + s₃`, modulo the row sums and `bᵗc = 1/2`
  have hid : (d.b 0 * (d.A 0 0 * d.c 0 + d.A 0 1 * d.c 1 + d.A 0 2 * d.c 2)
        + d.b 1 * (d.A 1 0 * d.c 0 + d.A 1 1 * d.c 1 + d.A 1 2 * d.c 2)
        + d.b 2 * (d.A 2 0 * d.c 0 + d.A 2 1 * d.c 1 + d.A 2 2 * d.c 2))
      - (d.c 0 / 2 + d.b 0 * (d.c 1 - d.c 0) * (d.c 0 - d.A 0 0)
        + d.b 1 * (d.c 1 - d.c 0) * d.A 1 1 + d.b 2 * (d.c 2 - d.c 0) * d.A 2 2)
      = d.b 0 * d.A 0 2 * (d.c 2 - d.c 1) + d.b 1 * d.A 1 2 * (d.c 2 - d.c 0)
        + d.b 2 * d.A 2 1 * (d.c 1 - d.c 0) := by
    linear_combination d.c 0 * h2 - (d.b 0 * d.c 1) * c0 - (d.b 1 * d.c 0) * c1
      - (d.b 2 * d.c 0) * c2
  linarith [h4, hid, s1, s2, s3]

/-- `β₁ + β₂ = 1/2 − c₀`, from `bᵗc = 1/2` and `bᵗe = 1`. -/
lemma beta_sum (_ : d.c 0 ≤ d.c 1) (_ : d.c 1 ≤ d.c 2) :
    d.b 1 * (d.c 1 - d.c 0) + d.b 2 * (d.c 2 - d.c 0) = 1/2 - d.c 0 := by
  have h1 := d.h1; have h2 := d.h2
  rw [sum3] at h1 h2
  linear_combination h2 - d.c 0 * h1

/-- **The `θ > 1` endgame, over plain reals.**  Given `0 ≤ c₀ ≤ 1/3`, diagonal entries
`d₁, d₂ ≥ 0` whose minimum satisfies the convex-combination bound, `u = d₁ + d₂ > 1 − c₀`,
and the lower bound `v ≥ (c₀+u)/2 − 1/6 − c₀u` on `v = d₁d₂`, one gets a contradiction with
`rank_two_key`.  Stated abstractly so that elaboration never has to unfold `Data`. -/
lemma theta_gt_one_arith (c0 d1 d2 : ℝ)
    (hc0 : 0 ≤ c0) (hc0le : c0 ≤ 1/3)
    (hmle : min d1 d2 ≤ (1/3 - c0)/(1 - 2*c0))
    (hulb : 1 - c0 < d1 + d2)
    (hvlb : (c0 + (d1 + d2))/2 - 1/6 - c0*(d1 + d2) ≤ d1 * d2) :
    False := by
  set u : ℝ := d1 + d2 with hu
  set v : ℝ := d1 * d2 with hv
  set g : ℝ := (1/3 - c0)/(1 - 2*c0) with hg
  set m : ℝ := min d1 d2 with hm
  have hden : (0:ℝ) < 1 - 2*c0 := by linarith
  have hgd : g * (1 - 2*c0) = 1/3 - c0 := by rw [hg, div_mul_cancel₀ _ (ne_of_gt hden)]
  -- `v = m(u − m)`
  have hvm : v = m * (u - m) := by
    rcases le_total d1 d2 with h | h
    · rw [hv, hu, hm, min_eq_left h]; ring
    · rw [hv, hu, hm, min_eq_right h]; ring
  -- `g < u/2`
  have hd6ne : (6*(1 - 2*c0)) ≠ 0 := ne_of_gt (by linarith)
  have hnum : (0:ℝ) < 6*c0^2 - 3*c0 + 1 := by
    nlinarith [sq_nonneg (4*c0 - 1), sq_nonneg c0]
  have hsplit : (1 - c0)/2 - g = (6*c0^2 - 3*c0 + 1)/(6*(1 - 2*c0)) := by
    rw [eq_div_iff hd6ne]; linear_combination (-6) * hgd
  have hgu : g < u/2 := by
    have hpos : (0:ℝ) < (1 - c0)/2 - g := by
      rw [hsplit]; exact div_pos hnum (by linarith)
    linarith
  -- `v ≤ g(u − g)`, since `t(u−t)` increases up to `u/2`
  have hmu : m ≤ u/2 := by
    rcases le_total d1 d2 with h | h
    · rw [hm, min_eq_left h, hu]; linarith
    · rw [hm, min_eq_right h, hu]; linarith
  have hvub : v ≤ g * (u - g) := by
    rw [hvm]
    have hfac : g * (u - g) - m * (u - m) = (g - m) * (u - g - m) := by ring
    have hf1 : 0 ≤ g - m := by rw [hg, hm] at *; linarith [hmle]
    have hf2 : 0 ≤ u - g - m := by linarith
    have := mul_nonneg hf1 hf2
    linarith [hfac, this]
  -- contradiction with `rank_two_key`
  have hkey := rank_two_key c0 u hc0 hc0le hulb
  rw [← hg] at hkey
  linarith [hvlb, hvub, hkey]

/-- **`θ > 1` is impossible in the rank-two case, under the ordering `c₀ ≤ c₁ ≤ c₂`.** -/
theorem theta_gt_one_impossible_ordered (hdet : 0 < kb11 d * kb22 d - (kb12 d) ^ 2)
    (h01 : d.c 0 ≤ d.c 1) (h12 : d.c 1 ≤ d.c 2) (hth : 1 < theta d) : False := by
  have hsharp := sharp_bound d h01 h12
  have hbsum := beta_sum d h01 h12
  have hb1 := d.hbnn 1 (by simp); have hb2 := d.hbnn 2 (by simp)
  have hc0nn := c_nonneg d 0 (by simp)
  have hd0 := diag_le d 0 (by simp)
  have hd1 := diag_le d 1 (by simp)
  have hd2 := diag_le d 2 (by simp)
  have hbeta1 : 0 ≤ d.b 1 * (d.c 1 - d.c 0) := mul_nonneg hb1 (by linarith)
  have hbeta2 : 0 ≤ d.b 2 * (d.c 2 - d.c 0) := mul_nonneg hb2 (by linarith)
  -- the middle term is nonnegative, so it can be dropped
  have hmid : 0 ≤ d.b 0 * (d.c 1 - d.c 0) * (d.c 0 - d.A 0 0) :=
    mul_nonneg (mul_nonneg (d.hbnn 0 (by simp)) (by linarith)) (by linarith)
  have hdrop : d.c 0 / 2 + d.b 1 * (d.c 1 - d.c 0) * d.A 1 1
      + d.b 2 * (d.c 2 - d.c 0) * d.A 2 2 ≤ 1/6 := by linarith
  -- `A₀₀ ≥ 0` and diagonal entries nonnegative
  have hA11 := d.hA 1 (by simp) 1 (by simp)
  have hA22 := d.hA 2 (by simp) 2 (by simp)
  -- `c₀ ≤ 1/3`
  have hc0le : d.c 0 ≤ 1/3 := by
    nlinarith [hdrop, hbeta1, hbeta2, hA11, hA22]
  -- `c₀ < 1/2`, so `β₁ + β₂ > 0`
  have hbpos : 0 < d.b 1 * (d.c 1 - d.c 0) + d.b 2 * (d.c 2 - d.c 0) := by
    rw [hbsum]; linarith
  -- `min(d₁,d₂) ≤ g(c₀)`
  have hmle : min (d.A 1 1) (d.A 2 2) ≤ (1/3 - d.c 0)/(1 - 2*d.c 0) := by
    have hden : (0:ℝ) < 1 - 2*d.c 0 := by linarith
    have hgd : ((1/3 - d.c 0)/(1 - 2*d.c 0)) * (1 - 2*d.c 0) = 1/3 - d.c 0 :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    set m : ℝ := min (d.A 1 1) (d.A 2 2) with hm
    have e1 : m ≤ d.A 1 1 := min_le_left _ _
    have e2 : m ≤ d.A 2 2 := min_le_right _ _
    have hconv : (1/2 - d.c 0) * m
        ≤ d.b 1 * (d.c 1 - d.c 0) * d.A 1 1 + d.b 2 * (d.c 2 - d.c 0) * d.A 2 2 := by
      have q1 := mul_le_mul_of_nonneg_left e1 hbeta1
      have q2 := mul_le_mul_of_nonneg_left e2 hbeta2
      have hsum : d.b 1 * (d.c 1 - d.c 0) * m + d.b 2 * (d.c 2 - d.c 0) * m
          = (1/2 - d.c 0) * m := by
        rw [← hbsum]; ring
      linarith [q1, q2, hsum]
    have hpos : (0:ℝ) < 1/2 - d.c 0 := by linarith
    have hstep : (1/2 - d.c 0) * m ≤ 1/6 - d.c 0/2 := by linarith [hdrop, hconv]
    have hgv : (1/2 - d.c 0) * ((1/3 - d.c 0)/(1 - 2*d.c 0)) = 1/6 - d.c 0/2 := by
      rw [mul_comm, div_mul_eq_mul_div, div_eq_iff (ne_of_gt hden)]
      ring
    rw [← hgv] at hstep
    exact le_of_mul_le_mul_left hstep hpos
  -- `u = d₁ + d₂ > 1 − c₀`
  have hulb : 1 - d.c 0 < d.A 1 1 + d.A 2 2 := by
    have hthe : theta d = d.A 0 0 + d.A 1 1 + d.A 2 2 := by simp only [theta]
    rw [hthe] at hth; linarith
  -- the lower bound on `v` from `Δ ≥ 0`
  have hDnn := sig2B_nonneg d hdet
  have hD := Delta_id d
  have hvlb : (d.c 0 + (d.A 1 1 + d.A 2 2))/2 - 1/6 - d.c 0 * (d.A 1 1 + d.A 2 2)
      ≤ d.A 1 1 * d.A 2 2 := by
    have p01 := mul_nonneg (d.hA 0 (by simp) 1 (by simp)) (d.hA 1 (by simp) 0 (by simp))
    have p02 := mul_nonneg (d.hA 0 (by simp) 2 (by simp)) (d.hA 2 (by simp) 0 (by simp))
    have p12 := mul_nonneg (d.hA 1 (by simp) 2 (by simp)) (d.hA 2 (by simp) 1 (by simp))
    have hid : d.A 0 0 * (d.A 1 1 + d.A 2 2) + d.A 1 1 * d.A 2 2 - sig2A d
        = d.A 0 1 * d.A 1 0 + d.A 0 2 * d.A 2 0 + d.A 1 2 * d.A 2 1 := by
      simp only [sig2A]; ring
    have hthe : theta d = d.A 0 0 + (d.A 1 1 + d.A 2 2) := by simp only [theta]; ring
    rw [hthe] at hD
    -- `Δ ≥ 0` ⟹ `d₀u + v ≥ (d₀+u)/2 − 1/6`; then `d₀ ≤ c₀` and slope `1/2 − u < 0`
    have step1 : (d.A 0 0 + (d.A 1 1 + d.A 2 2))/2 - 1/6
        ≤ d.A 0 0 * (d.A 1 1 + d.A 2 2) + d.A 1 1 * d.A 2 2 := by
      linarith [hDnn, hD, hid, p01, p02, p12]
    have hslope : (1:ℝ)/2 - (d.A 1 1 + d.A 2 2) ≤ 0 := by linarith
    have h1 : d.A 0 0 - d.c 0 ≤ 0 := by linarith
    have hprod : 0 ≤ (d.A 0 0 - d.c 0) * (1/2 - (d.A 1 1 + d.A 2 2)) :=
      mul_nonneg_of_nonpos_of_nonpos h1 hslope
    have hdiff : ((d.A 0 0 + (d.A 1 1 + d.A 2 2))/2 - 1/6
          - d.A 0 0 * (d.A 1 1 + d.A 2 2))
        - ((d.c 0 + (d.A 1 1 + d.A 2 2))/2 - 1/6 - d.c 0 * (d.A 1 1 + d.A 2 2))
        = (d.A 0 0 - d.c 0) * (1/2 - (d.A 1 1 + d.A 2 2)) := by ring
    linarith [step1, hprod, hdiff]
  exact theta_gt_one_arith (d.c 0) (d.A 1 1) (d.A 2 2) hc0nn hc0le hmle hulb hvlb


/-! ### The ordering WLOG

Every hypothesis of `Data` is invariant under simultaneously permuting the rows and columns of
`A` and `R` and the coordinates of `b` and `c`.  Over `range 3` the cleanest route is to build
the relabelled structure explicitly from a permutation given as a triple of indices: all sums
are three-term, so each field is a finite rearrangement that `simp` + `linarith`/`ring` settle
without any reindexing lemmas. -/

/-- Relabel `Data` along the permutation sending `0 ↦ p₀`, `1 ↦ p₁`, `2 ↦ p₂`, where
`(p₀,p₁,p₂)` is a permutation of `(0,1,2)` — supplied as the hypothesis `hperm` listing the
six admissible triples. -/
noncomputable def relab (p0 p1 p2 : ℕ) : ℕ → ℕ :=
  fun i => if i = 0 then p0 else if i = 1 then p1 else p2

/-- The six permutations of `(0,1,2)`. -/
def IsPerm3 (p0 p1 p2 : ℕ) : Prop :=
  (p0 = 0 ∧ p1 = 1 ∧ p2 = 2) ∨ (p0 = 0 ∧ p1 = 2 ∧ p2 = 1) ∨
  (p0 = 1 ∧ p1 = 0 ∧ p2 = 2) ∨ (p0 = 1 ∧ p1 = 2 ∧ p2 = 0) ∨
  (p0 = 2 ∧ p1 = 0 ∧ p2 = 1) ∨ (p0 = 2 ∧ p1 = 1 ∧ p2 = 0)

/-- A relabelling by a permutation of `(0,1,2)` maps `range 3` into itself. -/
lemma relab_mem (p0 p1 p2 : ℕ) (hp : IsPerm3 p0 p1 p2) (i : ℕ) (hi : i ∈ range 3) :
    relab p0 p1 p2 i ∈ range 3 := by
  have hi' := mem_range.1 hi
  rcases hp with ⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩ <;>
    subst a <;> subst b <;> subst c <;>
    interval_cases i <;> simp only [relab] <;> norm_num

/-- Relabelled data.  Every field is proved by expanding the three-term sums and dispatching
on which of the six permutations is in play. -/
noncomputable def permData (p0 p1 p2 : ℕ) (hp : IsPerm3 p0 p1 p2) : Data where
  A := fun i j => d.A (relab p0 p1 p2 i) (relab p0 p1 p2 j)
  R := fun i j => d.R (relab p0 p1 p2 i) (relab p0 p1 p2 j)
  b := fun i => d.b (relab p0 p1 p2 i)
  c := fun i => d.c (relab p0 p1 p2 i)
  hA := fun i hi j hj =>
    d.hA _ (relab_mem p0 p1 p2 hp i hi) _ (relab_mem p0 p1 p2 hp j hj)
  hRsymm := fun i hi j hj =>
    d.hRsymm _ (relab_mem p0 p1 p2 hp i hi) _ (relab_mem p0 p1 p2 hp j hj)
  hRpsd := by
    intro x
    have h := d.hRpsd (fun k => if k = p0 then x 0 else if k = p1 then x 1 else x 2)
    simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
      relab] at h ⊢
    rcases hp with ⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩ <;>
      subst a <;> subst b <;> subst c <;> norm_num at h ⊢ <;> linarith [h]
  hb := by
    intro i hi
    have hi' := mem_range.1 hi
    have h := d.hb (relab p0 p1 p2 i) (relab_mem p0 p1 p2 hp i hi)
    simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
      relab] at h ⊢
    rcases hp with ⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩ <;>
      subst a <;> subst b <;> subst c <;> norm_num at h ⊢ <;>
      (interval_cases i <;> norm_num at h ⊢ <;> linarith [h])
  hbnn := fun i hi => d.hbnn _ (relab_mem p0 p1 p2 hp i hi)
  hc := by
    intro i hi
    have hi' := mem_range.1 hi
    have h := d.hc (relab p0 p1 p2 i) (relab_mem p0 p1 p2 hp i hi)
    simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
      relab] at h ⊢
    rcases hp with ⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩ <;>
      subst a <;> subst b <;> subst c <;> norm_num at h ⊢ <;>
      (interval_cases i <;> norm_num at h ⊢ <;> linarith [h])
  hMpsd := by
    intro x
    have h := d.hMpsd (fun k => if k = p0 then x 0 else if k = p1 then x 1 else x 2)
    simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
      relab] at h ⊢
    rcases hp with ⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩ <;>
      subst a <;> subst b <;> subst c <;> norm_num at h ⊢ <;> linarith [h]
  h1 := by
    have h := d.h1
    rw [sum3] at h
    simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, relab]
    rcases hp with ⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩ <;>
      subst a <;> subst b <;> subst c <;> norm_num <;> linarith [h]
  h2 := by
    have h := d.h2
    rw [sum3] at h
    simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, relab]
    rcases hp with ⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩ <;>
      subst a <;> subst b <;> subst c <;> norm_num <;> linarith [h]
  h3 := by
    have h := d.h3
    rw [sum3] at h
    simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, relab]
    rcases hp with ⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩ <;>
      subst a <;> subst b <;> subst c <;> norm_num <;> linarith [h]
  h4 := by
    have h := d.h4
    simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
      relab] at h ⊢
    rcases hp with ⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩ <;>
      subst a <;> subst b <;> subst c <;> norm_num at h ⊢ <;> linarith [h]


/-- `theta` is permutation-invariant: relabelling permutes the diagonal of `A`. -/
lemma theta_permData (p0 p1 p2 : ℕ) (hp : IsPerm3 p0 p1 p2) :
    theta (permData d p0 p1 p2 hp) = theta d := by
  simp only [theta, permData, relab]
  rcases hp with ⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩ <;>
    subst a <;> subst b <;> subst c <;> norm_num <;> ring

/-- `det K̄` is permutation-invariant.  The permutation fixes `e`, so it induces a map of the
quotient `ℝ³/⟨e⟩` of determinant `±1`, and `det K̄` — a determinant on that quotient — is
unchanged. -/
lemma detKb_permData (p0 p1 p2 : ℕ) (hp : IsPerm3 p0 p1 p2) :
    kb11 (permData d p0 p1 p2 hp) * kb22 (permData d p0 p1 p2 hp)
      - (kb12 (permData d p0 p1 p2 hp)) ^ 2
    = kb11 d * kb22 d - (kb12 d) ^ 2 := by
  have s01 := d.hRsymm 0 (by simp) 1 (by simp)
  have s02 := d.hRsymm 0 (by simp) 2 (by simp)
  have s12 := d.hRsymm 1 (by simp) 2 (by simp)
  have k0 := Km_e d 0 (by simp)
  have k1 := Km_e d 1 (by simp)
  have k2 := Km_e d 2 (by simp)
  simp only [show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero] at k0 k1 k2
  simp only [kb11, kb12, kb22, Kpair, Km, permData, relab, f1, f2,
    show (3:ℕ)=2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Km] at k0 k1 k2
  rcases hp with ⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩ <;>
    subst a <;> subst b <;> subst c <;> norm_num
  · linear_combination ((d.R 0 1) - (d.R 0 2) - (d.R 1 0) + (d.R 1 2) + (d.R 2 0) - (d.R 2 1))*k0 + (3*(d.R 0 1) - 3*(d.R 0 2) - 3*(d.R 1 0) + 3*(d.R 1 2) + 3*(d.R 2 0) - 3*(d.R 2 1))*k1 + (-(d.R 0 1) + (d.R 0 2) + (d.R 1 0) - (d.R 1 2) - (d.R 2 0) + (d.R 2 1))*k2 + (-(d.R 0 0) - (d.R 0 1) - 4*(d.R 0 2) - 3*(d.R 1 0) - 4*(d.R 1 1) + (d.R 1 2) + 4*(d.R 2 0) - (d.R 2 1) + (d.b 0)^2 + 4*(d.b 0)*(d.b 1) + 4*(d.b 1)^2)*s01 + ((d.R 0 0) + 4*(d.R 0 1) + (d.R 0 2) + 4*(d.R 1 1) + (d.R 1 2) - (d.R 2 0) - (d.R 2 1) - (d.b 0)^2 - 4*(d.b 0)*(d.b 1) - 4*(d.b 1)^2)*s02 + (-(d.R 0 0) - 4*(d.R 0 1) - 4*(d.R 1 1) - 2*(d.R 1 2) + 2*(d.R 2 1) + (d.b 0)^2 + 4*(d.b 0)*(d.b 1) + 4*(d.b 1)^2)*s12
  · linear_combination (-(d.R 0 0) + (d.R 0 1) + (d.R 0 2) + (d.R 1 0) - (d.R 1 1) - (d.R 1 2) - (d.R 2 0) + (d.R 2 1) + (d.b 0)^2 - 2*(d.b 0)*(d.b 1) + (d.b 1)^2)*s01 + ((d.R 0 0) - 2*(d.R 0 1) + (d.R 1 1) - (d.b 0)^2 + 2*(d.b 0)*(d.b 1) - (d.b 1)^2)*s02 + (-(d.R 0 0) + 2*(d.R 0 1) - (d.R 1 1) + (d.b 0)^2 - 2*(d.b 0)*(d.b 1) + (d.b 1)^2)*s12
  · linear_combination (-3*(d.R 0 1) + 3*(d.R 0 2) + 3*(d.R 1 0) - 3*(d.R 1 2) - 3*(d.R 2 0) + 3*(d.R 2 1))*k0 + (-(d.R 0 1) + (d.R 0 2) + (d.R 1 0) - (d.R 1 2) - (d.R 2 0) + (d.R 2 1))*k1 + ((d.R 0 1) - (d.R 0 2) - (d.R 1 0) + (d.R 1 2) + (d.R 2 0) - (d.R 2 1))*k2 + (3*(d.R 0 0) + 4*(d.R 0 1) + 4*(d.R 0 2) + 2*(d.R 1 0) - (d.R 1 2) - 4*(d.R 2 0) + (d.R 2 1) - 3*(d.b 0)^2 - 6*(d.b 0)*(d.b 1))*s01 + (-3*(d.R 0 0) - 6*(d.R 0 1) - 2*(d.R 0 2) + (d.R 1 2) + 2*(d.R 2 0) - (d.R 2 1) + 3*(d.b 0)^2 + 6*(d.b 0)*(d.b 1))*s02 + (3*(d.R 0 0) + 6*(d.R 0 1) + (d.R 1 2) - (d.R 2 1) - 3*(d.b 0)^2 - 6*(d.b 0)*(d.b 1))*s12
  · linear_combination (-2*(d.R 0 1) + 2*(d.R 0 2) + 2*(d.R 1 0) - 2*(d.R 1 2) - 2*(d.R 2 0) + 2*(d.R 2 1))*k0 + (2*(d.R 0 1) - 2*(d.R 0 2) - 2*(d.R 1 0) + 2*(d.R 1 2) + 2*(d.R 2 0) - 2*(d.R 2 1))*k1 + (3*(d.R 0 0) + 2*(d.R 0 1) - (d.R 0 2) - 2*(d.R 1 0) - 3*(d.R 1 1) + (d.R 1 2) + (d.R 2 0) - (d.R 2 1) - 3*(d.b 0)^2 + 3*(d.b 1)^2)*s01 + (-3*(d.R 0 0) - (d.R 0 2) + 3*(d.R 1 1) + 2*(d.R 1 2) + (d.R 2 0) - 2*(d.R 2 1) + 3*(d.b 0)^2 - 3*(d.b 1)^2)*s02 + (3*(d.R 0 0) - 3*(d.R 1 1) - (d.R 1 2) + (d.R 2 1) - 3*(d.b 0)^2 + 3*(d.b 1)^2)*s12
  · linear_combination (-2*(d.R 0 1) + 2*(d.R 0 2) + 2*(d.R 1 0) - 2*(d.R 1 2) - 2*(d.R 2 0) + 2*(d.R 2 1))*k0 + (2*(d.R 0 1) - 2*(d.R 0 2) - 2*(d.R 1 0) + 2*(d.R 1 2) + 2*(d.R 2 0) - 2*(d.R 2 1))*k1 + (2*(d.R 0 0) + 3*(d.R 0 1) - (d.R 1 0) - 4*(d.R 1 1) - 2*(d.b 0)^2 - 2*(d.b 0)*(d.b 1) + 4*(d.b 1)^2)*s01 + (-2*(d.R 0 0) - 2*(d.R 0 1) - (d.R 0 2) + 4*(d.R 1 1) + 2*(d.R 1 2) + (d.R 2 0) - 2*(d.R 2 1) + 2*(d.b 0)^2 + 2*(d.b 0)*(d.b 1) - 4*(d.b 1)^2)*s02 + (2*(d.R 0 0) + 2*(d.R 0 1) - 4*(d.R 1 1) - (d.R 1 2) + (d.R 2 1) - 2*(d.b 0)^2 - 2*(d.b 0)*(d.b 1) + 4*(d.b 1)^2)*s12

/-- **`θ > 1` is impossible in the rank-two case**, with no ordering assumption: relabel so
that `c₀ ≤ c₁ ≤ c₂` (six cases), using that `theta` and `det K̄` are permutation-invariant. -/
theorem theta_gt_one_impossible (hdet : 0 < kb11 d * kb22 d - (kb12 d) ^ 2)
    (hth : 1 < theta d) : False := by
  -- pick the permutation that sorts `c`
  have key : ∀ (p0 p1 p2 : ℕ) (hp : IsPerm3 p0 p1 p2),
      (permData d p0 p1 p2 hp).c 0 ≤ (permData d p0 p1 p2 hp).c 1 →
      (permData d p0 p1 p2 hp).c 1 ≤ (permData d p0 p1 p2 hp).c 2 → False := by
    intro p0 p1 p2 hp h01 h12
    refine theta_gt_one_impossible_ordered (permData d p0 p1 p2 hp) ?_ h01 h12 ?_
    · rw [detKb_permData d p0 p1 p2 hp]; exact hdet
    · rw [theta_permData d p0 p1 p2 hp]; exact hth
  -- the six orderings
  simp only [permData, relab] at key
  rcases le_total (d.c 0) (d.c 1) with h01 | h01
  · rcases le_total (d.c 1) (d.c 2) with h12 | h12
    · exact key 0 1 2 (by tauto) (by norm_num [h01]) (by norm_num [h12])
    · rcases le_total (d.c 0) (d.c 2) with h02 | h02
      · exact key 0 2 1 (by tauto) (by norm_num [h02]) (by norm_num [h12])
      · exact key 2 0 1 (by tauto) (by norm_num [h02]) (by norm_num [h01])
  · rcases le_total (d.c 0) (d.c 2) with h02 | h02
    · exact key 1 0 2 (by tauto) (by norm_num [h01]) (by norm_num [h02])
    · rcases le_total (d.c 1) (d.c 2) with h12 | h12
      · exact key 1 2 0 (by tauto) (by norm_num [h12]) (by norm_num [h02])
      · exact key 2 1 0 (by tauto) (by norm_num [h12]) (by norm_num [h01])


/-! ## Theorem 1 -/

/-- **Theorem 1: the general Claim is inconsistent at `s = 3`.**

There is no `Data` — that is, no `3 × 3` tableau `A ≥ 0` with a symmetric positive semidefinite
`R` satisfying `Re = b`, `b ≥ 0`, `c = Ae`, `M = RA + AᵗR − bbᵗ ⪰ 0`, and the order conditions
`bᵗe = 1`, `bᵗc = 1/2`, `bᵗc² = 1/3`, `bᵗAc = 1/6`.

No sign condition on `R`, no distinctness of the `cᵢ`, no upper bound on `c`, and no strict
positivity of `b` is assumed.

The proof: `rank_dichotomy` splits on `det K̄`.  Rank one is impossible
(`rank_one_impossible`).  In the rank-two case `theta_ge_half` and `sig2B_nonneg` are theorems,
so `trichotomy_rank_two` leaves `θ = 1/2` or `θ ≥ 1`; the first is `theta_half_impossible`, and
`θ ≥ 1` splits into `θ = 1` (`theta_one_impossible_rank_two`) and `θ > 1`
(`theta_gt_one_impossible`). -/
theorem three_stage_claim_inconsistent : ¬ Nonempty Data := by
  rintro ⟨d⟩
  rcases rank_dichotomy d with hpos | hzero
  · -- rank two: the trichotomy on `θ`, all three branches excluded
    rcases trichotomy_rank_two d hpos with hhalf | hge
    · exact theta_half_impossible d hpos hhalf
    · rcases eq_or_lt_of_le hge with heq | hgt
      · exact theta_one_impossible_rank_two d hpos heq.symm
      · exact theta_gt_one_impossible d hpos hgt
  · -- rank one
    exact rank_one_impossible d hzero

/-- Restated as an explicit impossibility: no such tableau exists. -/
theorem no_three_stage_tableau
    (A R : ℕ → ℕ → ℝ) (b c : ℕ → ℝ)
    (hA : ∀ i ∈ range 3, ∀ j ∈ range 3, 0 ≤ A i j)
    (hRsymm : ∀ i ∈ range 3, ∀ j ∈ range 3, R i j = R j i)
    (hRpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 3, ∑ j ∈ range 3, R i j * (x i * x j))
    (hb : ∀ i ∈ range 3, b i = ∑ j ∈ range 3, R i j)
    (hbnn : ∀ i ∈ range 3, 0 ≤ b i)
    (hc : ∀ i ∈ range 3, c i = ∑ j ∈ range 3, A i j)
    (hMpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 3, ∑ j ∈ range 3,
      ((∑ k ∈ range 3, R i k * A k j) + (∑ k ∈ range 3, R j k * A k i) - b i * b j)
        * (x i * x j))
    (h1 : ∑ i ∈ range 3, b i = 1)
    (h2 : ∑ i ∈ range 3, b i * c i = 1/2)
    (h3 : ∑ i ∈ range 3, b i * (c i)^2 = 1/3)
    (h4 : ∑ i ∈ range 3, b i * ∑ j ∈ range 3, A i j * c j = 1/6) :
    False :=
  three_stage_claim_inconsistent
    ⟨{ A := A, R := R, b := b, c := c, hA := hA, hRsymm := hRsymm, hRpsd := hRpsd,
       hb := hb, hbnn := hbnn, hc := hc, hMpsd := hMpsd,
       h1 := h1, h2 := h2, h3 := h3, h4 := h4 }⟩


end ThreeStage

end SSP
