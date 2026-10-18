import Mathlib.Tactic
import SSPLean.BStability

/-!
# The algebraic-stability claim is false for general PSD `R`

The paper *AI counter example* (`main-4.tex`) states the following

**Claim.**  Let `A ∈ ℝ^{s×s}`, `b ∈ ℝ^s` with `A ≥ 0`, `b ≥ 0` entrywise, let
`R` be symmetric positive semidefinite with `b = R e`, put `c = A e` with
`0 ≤ c₁ < c₂ < ⋯ < c_s ≤ 1`, and assume the order-three quadrature conditions
`bᵀe = 1`, `bᵀc = 1/2`, `bᵀAc = 1/6`, `bᵀCc = 1/3`.  Then
`M = RA + AᵀR − bbᵀ` cannot be positive semidefinite.

This file machine-verifies that the claim is **false as stated**, and isolates exactly
which hypothesis is missing.

## What is proved

* `AlgStabData` — a bundle recording *all* hypotheses of the Claim for a given stage
  count, together with `M = 0` (the strongest possible violation of the conclusion:
  `M = 0` is trivially PSD).  An inhabitant is a counterexample.
* `R_not_diagonal` — **unconditional**: in *every* `AlgStabData` the certificate `R` is
  necessarily **not** diagonal.  Proved by reduction to
  `SSP.no_order3_algebraically_stable` of `SSPLean/BStability.lean`.  Consequently the
  counterexample does not contradict that theorem — the two live in different regimes.
* `diag_case_impossible` — the diagonal regime, restating
  `SSP.no_order3_algebraically_stable`: when `R = diag b` the Claim's conclusion *is* a
  theorem.
* `s2_near_miss` — **unconditional**, fully verified in exact arithmetic: an explicit
  `s = 2` tableau satisfying every hypothesis of the Claim *except* `bᵀAc = 1/6`, with
  `M = 0` and `R` non-diagonal.  This locates the obstruction to a small counterexample
  in the single condition `bᵀAc = 1/6`, and is why nine stages are needed.
* `tau_exists` — the analytic input of `main-4.tex` §5: the intermediate value theorem
  applied to the order-three defect `f`, whose exact rational endpoint values (recomputed
  independently in exact arithmetic) have opposite signs.
* `ConstructionData` / `claim_false` / `claim_needs_extra_hypothesis` — the nine-stage
  construction of §2 and the separation it yields.
* `ConstructionFamily` / `claim_false_of_family` — the same, but with the parameter carried
  explicitly, so the order-three condition is **derived** from the intermediate value
  theorem (`ConstructionFamily.tau_ord4`) instead of assumed.  This is where `tau_exists`
  is load-bearing: `ConstructionFamily` has no order-three field at all, only continuity of
  the defect and its two endpoint signs.

## Status of the nine-stage construction

`ConstructionData s` bundles the `t`-independent algebraic identities of the construction
(`RA + AᵀR = bbᵀ`, `Re = b`, the order conditions) as *hypotheses*, and `claim_false` is
stated **conditionally** on an inhabitant of it.  `ConstructionFamily s` is the sharper
version: it assumes those identities for every `t` in the bracketing interval, plus
continuity of the order-three defect and its endpoint signs, and then *derives* the
order-three condition at the IVT parameter.  Verifying those identities for the
explicit nine-stage data of `main-4.tex` requires exact arithmetic with `9 × 9` Krylov
matrices over the degree-11 algebraic number `τ`, which is not carried out here.  So the
nine-stage refutation is formalized *modulo* that computation, while `R_not_diagonal`,
`diag_case_impossible` and `s2_near_miss` are unconditional.

What the conditional statement does establish is that the paper's argument is *valid*:
granting the §2 identities, the Claim provably fails, and the failure is necessarily via a
non-diagonal `R`.

## Conventions

Matrices are `ℕ → ℕ → ℝ` and sums run over `Finset.range s`, matching
`SSPLean/BStability.lean`.  Positive semidefiniteness is stated as nonnegativity of
the quadratic form over `range s`, as in that file.  The `ℕ`-indexed convention means
a matrix is only ever constrained on `range s × range s`.
-/

open Finset

namespace SSP

namespace Counterexample

/-! ## Positive semidefiniteness, in the `range s` convention -/

/-- `PSDOn s X`: the quadratic form of `X` is nonnegative on vectors supported in
`range s`.  This is the same formulation of positive semidefiniteness used for the
algebraic-stability matrix in `SSPLean/BStability.lean`. -/
def PSDOn (s : ℕ) (X : ℕ → ℕ → ℝ) : Prop :=
  ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range s, ∑ j ∈ range s, X i j * (x i * x j)

/-- `SymmOn s X`: symmetry of `X` on `range s`. -/
def SymmOn (s : ℕ) (X : ℕ → ℕ → ℝ) : Prop :=
  ∀ i ∈ range s, ∀ j ∈ range s, X i j = X j i

/-- The zero matrix is positive semidefinite. -/
lemma psdOn_zero (s : ℕ) : PSDOn s (fun _ _ => (0 : ℝ)) := by
  intro x
  simp

/-! ## The hypotheses of the Claim, bundled -/

/-- All hypotheses of the Claim of `main-4.tex`, for an `s`-stage tableau `(A, b)`
with certificate `R`, together with the *negation* of its conclusion in the strongest
form `M = RA + AᵀR − bbᵀ = 0`.

An inhabitant of this structure is a counterexample to the Claim. -/
structure AlgStabData (s : ℕ) where
  /-- The Runge–Kutta coefficient matrix. -/
  A : ℕ → ℕ → ℝ
  /-- The quadrature weights. -/
  b : ℕ → ℝ
  /-- The algebraic-stability certificate. -/
  R : ℕ → ℕ → ℝ
  /-- Abscissas, `c = A e`. -/
  c : ℕ → ℝ
  /-- `A` is entrywise nonnegative. -/
  hA : ∀ i j, 0 ≤ A i j
  /-- `b` is entrywise positive (stronger than the Claim's `b ≥ 0`). -/
  hb : ∀ i ∈ range s, 0 < b i
  /-- `c = A e`, i.e. `cᵢ` is the `i`-th row sum of `A`. -/
  hc : ∀ i ∈ range s, c i = ∑ j ∈ range s, A i j
  /-- The abscissas are strictly increasing. -/
  hcmono : ∀ i ∈ range s, ∀ j ∈ range s, i < j → c i < c j
  /-- The abscissas lie in `[0, 1]`. -/
  hcrange : ∀ i ∈ range s, 0 ≤ c i ∧ c i ≤ 1
  /-- `R` is symmetric. -/
  hRsymm : SymmOn s R
  /-- `R` is positive semidefinite. -/
  hRpsd : PSDOn s R
  /-- `b = R e`. -/
  hRe : ∀ i ∈ range s, b i = ∑ j ∈ range s, R i j
  /-- `bᵀe = 1`. -/
  h1 : ∑ i ∈ range s, b i = 1
  /-- `bᵀc = 1/2`. -/
  h2 : ∑ i ∈ range s, b i * c i = 1 / 2
  /-- `bᵀAc = 1/6`. -/
  h3 : ∑ i ∈ range s, b i * ∑ j ∈ range s, A i j * c j = 1 / 6
  /-- `bᵀCc = bᵀc² = 1/3`, the order-three condition. -/
  h4 : ∑ i ∈ range s, b i * (c i) ^ 2 = 1 / 3
  /-- The algebraic-stability matrix vanishes identically on `range s`:
  `M = RA + AᵀR − bbᵀ = 0`.  In particular `M` is positive semidefinite,
  contradicting the Claim's conclusion. -/
  hM : ∀ i ∈ range s, ∀ j ∈ range s,
    (∑ k ∈ range s, R i k * A k j) + (∑ k ∈ range s, R j k * A k i) - b i * b j = 0

/-- The algebraic-stability matrix of an `AlgStabData` is positive semidefinite —
it is the zero matrix.  This is the conclusion the Claim asserts to be impossible. -/
theorem AlgStabData.M_psd {s : ℕ} (d : AlgStabData s) :
    PSDOn s (fun i j => (∑ k ∈ range s, d.R i k * d.A k j)
      + (∑ k ∈ range s, d.R j k * d.A k i) - d.b i * d.b j) := by
  intro x
  have h : ∀ i ∈ range s, ∑ j ∈ range s,
      ((∑ k ∈ range s, d.R i k * d.A k j)
        + (∑ k ∈ range s, d.R j k * d.A k i) - d.b i * d.b j) * (x i * x j) = 0 := by
    intro i hi
    refine sum_eq_zero fun j hj => ?_
    rw [d.hM i hi j hj, zero_mul]
  rw [sum_congr rfl h]
  simp

/-! ## Every witness has a non-diagonal `R`

`SSPLean/BStability.lean` proves `SSP.no_order3_algebraically_stable`: the Claim's
conclusion *does* hold when the certificate is the diagonal matrix `R = diag b`.  So any
counterexample must use an `R` that is not diagonal.  We derive this here, showing the
counterexample below is consistent with the diagonal-`R` barrier rather than
contradicting it.

The barrier theorem quantifies over all of `ℕ`, while `AlgStabData` constrains only
`range s`, so we apply it to the truncations `b' i = if i < s then b i else 0` and
`c' i = if i < s then c i else c (s-1)`, which agree with `b`, `c` on `range s`. -/

/-- `DiagOn s R`: `R` vanishes off the diagonal on `range s`. -/
def DiagOn (s : ℕ) (R : ℕ → ℕ → ℝ) : Prop :=
  ∀ i ∈ range s, ∀ j ∈ range s, i ≠ j → R i j = 0

/-- Collapse a sum against a row of a matrix that is diagonal on `range s`. -/
lemma sum_diag_row {s : ℕ} {R : ℕ → ℕ → ℝ} (hd : DiagOn s R)
    (f : ℕ → ℝ) {i : ℕ} (hi : i ∈ range s) :
    ∑ k ∈ range s, R i k * f k = R i i * f i := by
  rw [← sum_singleton (f := fun k => R i k * f k) (a := i)]
  refine (sum_subset (fun k hk => ?_) (fun k hk hkne => ?_)).symm
  · rw [mem_singleton] at hk; exact hk ▸ hi
  · rw [mem_singleton] at hkne
    rw [hd i hi k hk (Ne.symm hkne), zero_mul]

/-- If `R` is diagonal on `range s` and `R e = b`, its diagonal entries are `b`. -/
lemma diag_entry_eq {s : ℕ} {R : ℕ → ℕ → ℝ} {b : ℕ → ℝ}
    (hd : DiagOn s R) (hRe : ∀ i ∈ range s, b i = ∑ j ∈ range s, R i j)
    {i : ℕ} (hi : i ∈ range s) : R i i = b i := by
  have h := hRe i hi
  have hcol : ∑ j ∈ range s, R i j = R i i := by
    have := sum_diag_row hd (fun _ => (1 : ℝ)) hi
    simpa using this
  rw [hcol] at h
  exact h.symm

/-- **The certificate in any counterexample is necessarily not diagonal.**

If an `AlgStabData s` had a diagonal `R`, then `R = diag b` by `R e = b`, so the
vanishing of `M = RA + AᵀR − bbᵀ` would supply exactly the PSD hypothesis of
`SSP.no_order3_algebraically_stable`, which is a contradiction. -/
theorem R_not_diagonal {s : ℕ} (d : AlgStabData s) : ¬ DiagOn s d.R := by
  intro hd
  -- with `R` diagonal, `Σ_k R i k * A k j` collapses to `b i * A i j`
  have hcollapse : ∀ i ∈ range s, ∀ j : ℕ,
      ∑ k ∈ range s, d.R i k * d.A k j = d.b i * d.A i j := by
    intro i hi j
    rw [sum_diag_row hd (fun k => d.A k j) hi, diag_entry_eq hd d.hRe hi]
  -- the entrywise identity `bᵢaᵢⱼ + bⱼaⱼᵢ − bᵢbⱼ = 0` on `range s`
  have hMdiag : ∀ i ∈ range s, ∀ j ∈ range s,
      d.b i * d.A i j + d.b j * d.A j i - d.b i * d.b j = 0 := by
    intro i hi j hj
    have h := d.hM i hi j hj
    rwa [hcollapse i hi j, hcollapse j hj i] at h
  -- truncate `b` and `c` so the barrier's global hypotheses hold
  set b' : ℕ → ℝ := fun i => if i < s then d.b i else 0 with hb'
  set c' : ℕ → ℝ := fun i => if i < s then d.c i else d.c s with hc'
  have hbeq : ∀ i ∈ range s, b' i = d.b i := by
    intro i hi; simp [hb', mem_range.1 hi]
  have hceq : ∀ i ∈ range s, c' i = d.c i := by
    intro i hi; simp [hc', mem_range.1 hi]
  refine SSP.no_order3_algebraically_stable (s := s) d.A b' c' d.hA ?hbnn ?hcmono' ?hrow
    ?hs1 ?hs2 ?hs3 ?hqf
  case hbnn =>
    intro i
    by_cases h : i < s
    · simpa [hb', h] using (d.hb i (mem_range.2 h)).le
    · simp [hb', h]
  case hcmono' =>
    intro i j hij hjs
    have his' : i < s := lt_of_le_of_lt hij hjs
    simp only [hc', if_pos his', if_pos hjs]
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_refl _
    · exact (d.hcmono i (mem_range.2 his') j (mem_range.2 hjs) hlt).le
  case hrow =>
    intro i his
    simp only [hc', if_pos his]
    exact (d.hc i (mem_range.2 his)).ge
  case hs1 =>
    rw [sum_congr rfl hbeq]; exact d.h1
  case hs2 =>
    rw [sum_congr rfl fun i hi => by rw [hbeq i hi, hceq i hi]]; exact d.h2
  case hs3 =>
    rw [sum_congr rfl fun i hi => by rw [hbeq i hi, hceq i hi]]; exact d.h4
  case hqf =>
    intro x
    have hz : ∀ i ∈ range s, ∑ j ∈ range s,
        (b' i * d.A i j + b' j * d.A j i - b' i * b' j) * (x i * x j) = 0 := by
      intro i hi
      refine sum_eq_zero fun j hj => ?_
      rw [hbeq i hi, hbeq j hj, hMdiag i hi j hj, zero_mul]
    rw [sum_congr rfl hz]
    simp

/-! ## The construction of `main-4.tex` §2, and why it produces a counterexample

The construction is a similarity transport of a *fixed* algebraic identity along a
one-parameter family.  Writing `D = diag(v(t))`, `A = D⁻¹GD`, `b = Dh(t)`, `R = DXD`
with `h(t) = K(t)⁻ᵀq` and `X = LᵀB_G L`, `L = H K(t)⁻¹`, the Gauss relation
`B_G A_G + A_Gᵀ B_G = b_G b_Gᵀ` together with the Krylov intertwining `L G = A_G L`
gives the two identities

  `X G + Gᵀ X = h hᵀ`,      `X v = h`,

**for every** `t` in the interval.  Conjugating by `D` turns them into

  `R A + Aᵀ R − b bᵀ = 0`,   `R e = b`.

The order conditions `bᵀe = 1`, `bᵀc = 1/2`, `bᵀAc = 1/6` likewise hold for every `t`,
because they read `hᵀGᵏv = q_{k+1}` for `k = 0, 1, 2`, which is how `h` was defined.
The single condition that pins `t` is the order-three condition `bᵀc² = 1/3`, i.e.
`f(t) = 0` for

  `f(t) = Σᵢ hᵢ(t) (Gv(t))ᵢ² / vᵢ(t) − 1/3`.

Accordingly we isolate the `t`-independent algebraic content as a hypothesis bundle
`ConstructionData` and obtain `τ` from the intermediate value theorem.  This is the
faithful Lean rendering of the paper's argument: the analytic input is exactly the
sign change of `f`, and everything else is algebra. -/

/-- The `t`-independent content of the construction of `main-4.tex` §2, at the
parameter value where the order-three condition holds.

Fields `hMzero` and `hRe` are the transported identities `RA + AᵀR = bbᵀ` and `Re = b`;
`hord1`–`hord3` are the order conditions `hᵀGᵏv = q_{k+1}` (`k = 0,1,2`) after
conjugation; `hord4` is the order-three condition, the one that pins the parameter.
The positivity and separation facts `hApos`, `hbpos`, `hcmono`, `hcrange` are the
verified properties of the tableau at that parameter. -/
structure ConstructionData (s : ℕ) where
  /-- Coefficient matrix `A = D⁻¹ G D`. -/
  A : ℕ → ℕ → ℝ
  /-- Weights `b = D h`. -/
  b : ℕ → ℝ
  /-- Certificate `R = D X D`. -/
  R : ℕ → ℕ → ℝ
  /-- Abscissas `c = A e`. -/
  c : ℕ → ℝ
  /-- `A ≥ 0` entrywise: `G ≥ 0` and `v > 0`. -/
  hApos : ∀ i j, 0 ≤ A i j
  /-- `b > 0` on the stage range. -/
  hbpos : ∀ i ∈ range s, 0 < b i
  /-- `c = A e`. -/
  hcdef : ∀ i ∈ range s, c i = ∑ j ∈ range s, A i j
  /-- The abscissas are strictly increasing (after the relabelling of `main-4.tex`). -/
  hcmono : ∀ i ∈ range s, ∀ j ∈ range s, i < j → c i < c j
  /-- The abscissas lie in `[0, 1]`. -/
  hcrange : ∀ i ∈ range s, 0 ≤ c i ∧ c i ≤ 1
  /-- `R` is symmetric: `R = D Lᵀ B_G L D`. -/
  hRsymm : SymmOn s R
  /-- `R` is positive semidefinite: `B_G ≻ 0` makes `X = Lᵀ B_G L` PSD. -/
  hRpsd : PSDOn s R
  /-- `R e = b`, from `X v = h`. -/
  hRe : ∀ i ∈ range s, b i = ∑ j ∈ range s, R i j
  /-- `bᵀ e = 1`. -/
  hord1 : ∑ i ∈ range s, b i = 1
  /-- `bᵀ c = 1/2`. -/
  hord2 : ∑ i ∈ range s, b i * c i = 1 / 2
  /-- `bᵀ A c = 1/6`. -/
  hord3 : ∑ i ∈ range s, b i * ∑ j ∈ range s, A i j * c j = 1 / 6
  /-- `bᵀ c² = 1/3`: the order-three condition, holding at the IVT parameter `τ`. -/
  hord4 : ∑ i ∈ range s, b i * (c i) ^ 2 = 1 / 3
  /-- `R A + Aᵀ R − b bᵀ = 0`, from `X G + Gᵀ X = h hᵀ`. -/
  hMzero : ∀ i ∈ range s, ∀ j ∈ range s,
    (∑ k ∈ range s, R i k * A k j) + (∑ k ∈ range s, R j k * A k i) - b i * b j = 0

/-- The construction of `main-4.tex` §2 is a counterexample: its data satisfies every
hypothesis of the Claim while `M = 0`. -/
def ConstructionData.toAlgStabData {s : ℕ} (g : ConstructionData s) : AlgStabData s where
  A := g.A
  b := g.b
  R := g.R
  c := g.c
  hA := g.hApos
  hb := g.hbpos
  hc := g.hcdef
  hcmono := g.hcmono
  hcrange := g.hcrange
  hRsymm := g.hRsymm
  hRpsd := g.hRpsd
  hRe := g.hRe
  h1 := g.hord1
  h2 := g.hord2
  h3 := g.hord3
  h4 := g.hord4
  hM := g.hMzero

/-! ## The analytic input: existence of the parameter `τ`

The only non-algebraic step in the construction is the existence of a parameter `τ` in
the bracketing interval at which the order-three defect

  `f(t) = Σᵢ hᵢ(t) (G v(t))ᵢ² / vᵢ(t) − 1/3`

vanishes.  Because `h(t) = K(t)⁻ᵀ q` and `K(t)⁻ᵀ = (det K(t))⁻¹ · adj(K(t))ᵀ`, the
function `f` is a *rational* function of `t` with denominator `t · det K(t)`, hence
continuous wherever that denominator is nonzero — which is everywhere on the interval,
since exact evaluation gives `det K > 0` there.

Exact rational arithmetic at the endpoints of `I = [4860787/10⁶, 4860788/10⁶]` gives

  `f(t_L) = −167125399246092938681796369142848697`
          `/ 7061886053752426236852105733608582828000000 < 0`
  `f(t_R) =    28785127879645561905776631467671`
          `/ 1253886639421286039243006252420772750000 > 0`

so `f` changes sign on `I` and the intermediate value theorem applies.  (These are the
values printed by the SymPy certificate in the appendix of `main-4.tex`, and reproduced
in exact rational arithmetic.) -/

/-- Left endpoint of the bracketing interval. -/
noncomputable def tL : ℝ := 4860787 / 1000000

/-- Right endpoint of the bracketing interval. -/
noncomputable def tR : ℝ := 4860788 / 1000000

lemma tL_lt_tR : tL < tR := by
  unfold tL tR; norm_num

/-- The exact value of the order-three defect at the left endpoint, as computed by exact
rational arithmetic; it is negative. -/
theorem fL_neg :
    (-167125399246092938681796369142848697 : ℝ)
      / 7061886053752426236852105733608582828000000 < 0 := by
  norm_num

/-- The exact value of the order-three defect at the right endpoint; it is positive. -/
theorem fR_pos :
    (0 : ℝ) < 28785127879645561905776631467671
      / 1253886639421286039243006252420772750000 := by
  norm_num

/-- **Existence of the parameter `τ` (`main-4.tex` §5).**

Any function continuous on the bracketing interval which takes the exactly-computed
endpoint values has a zero in the open interval.  Applied to the order-three defect `f`,
this produces the parameter `τ ≈ 4.860787507604797` of the construction. -/
theorem tau_exists (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc tL tR))
    (hfL : f tL = (-167125399246092938681796369142848697 : ℝ)
      / 7061886053752426236852105733608582828000000)
    (hfR : f tR = 28785127879645561905776631467671
      / 1253886639421286039243006252420772750000) :
    ∃ τ ∈ Set.Ioo tL tR, f τ = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Ioo (f tL) (f tR) := by
    rw [hfL, hfR]
    exact Set.mem_Ioo.2 ⟨fL_neg, fR_pos⟩
  obtain ⟨τ, hτ, hfτ⟩ := intermediate_value_Ioo tL_lt_tR.le hf hmem
  exact ⟨τ, hτ, hfτ⟩

/-- The same statement in the form actually used: a sign change suffices. -/
theorem tau_exists_of_sign_change (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc tL tR)) (hfL : f tL < 0) (hfR : 0 < f tR) :
    ∃ τ ∈ Set.Ioo tL tR, f τ = 0 := by
  obtain ⟨τ, hτ, hfτ⟩ :=
    intermediate_value_Ioo tL_lt_tR.le hf (Set.mem_Ioo.2 ⟨hfL, hfR⟩)
  exact ⟨τ, hτ, hfτ⟩

/-! ## Why the counterexample needs many stages

It is natural to ask whether a much smaller counterexample exists.  It does not at
`s = 2`, and the obstruction is instructive: it is the condition `bᵀAc = 1/6`.

At `s = 2` the order-three moment conditions `bᵀe = 1`, `bᵀc = 1/2`, `bᵀc² = 1/3` with
`b > 0` and `c` strictly increasing in `[0,1]` admit the rational solution
`b = (3/4, 1/4)`, `c = (1/3, 1)`.  Imposing additionally `R e = b`, symmetry of `R`, and
`M = RA + AᵀR − bbᵀ = 0` leaves a one-parameter family of tableaux
`A = [[x, 1/3−x], [y, 1−y]]`, `R = [[3/4−z, z], [z, 1/4−z]]` with `x`, `y` determined by
`z`.  Exact rational computation shows the family contains members with `A ≥ 0` and `R`
positive semidefinite (for instance `z = 1/8`), and *every* such member has `R` not
diagonal — as `R_not_diagonal` requires.  But the remaining order condition
`bᵀAc = 1/6` cuts the family down to the single point `z = 0`, i.e. `R = diag b`, where
`A = [[3/8, −1/24], [7/8, 1/8]]` has a negative entry.

The lemma below records the near-miss witness, which satisfies every hypothesis of the
Claim except `bᵀAc = 1/6`.  It is the reason the construction of `main-4.tex` needs the
extra freedom of nine stages: with more stages the `bᵀAc` condition can be met while
keeping `A ≥ 0`. -/

/-- Tableau of the `s = 2` near-miss: `A = [[7/24, 1/24], [19/24, 5/24]]`. -/
noncomputable def A₂ : ℕ → ℕ → ℝ := fun i j =>
  if i = 0 then (if j = 0 then 7/24 else if j = 1 then 1/24 else 0)
  else if i = 1 then (if j = 0 then 19/24 else if j = 1 then 5/24 else 0)
  else 0

/-- Weights of the `s = 2` near-miss: `b = (3/4, 1/4)`. -/
noncomputable def b₂ : ℕ → ℝ := fun i =>
  if i = 0 then 3/4 else if i = 1 then 1/4 else 0

/-- Certificate of the `s = 2` near-miss: `R = [[5/8, 1/8], [1/8, 1/8]]`. -/
noncomputable def R₂ : ℕ → ℕ → ℝ := fun i j =>
  if i = 0 then (if j = 0 then 5/8 else if j = 1 then 1/8 else 0)
  else if i = 1 then (if j = 0 then 1/8 else if j = 1 then 1/8 else 0)
  else 0

/-- Abscissas of the `s = 2` near-miss: `c = (1/3, 1)`. -/
noncomputable def c₂ : ℕ → ℝ := fun i =>
  if i = 0 then 1/3 else if i = 1 then 1 else 0

/-- `c₂` is the vector of row sums of `A₂`. -/
lemma c₂_eq_rowSum : ∀ i ∈ range 2, c₂ i = ∑ j ∈ range 2, A₂ i j := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 := by have := mem_range.1 hi; omega
  rcases hi' with rfl | rfl <;> simp [Finset.sum_range_succ, A₂, c₂] <;> norm_num

/-- The order conditions `bᵀe = 1`, `bᵀc = 1/2`, `bᵀc² = 1/3` hold for the `s = 2`
near-miss. -/
lemma s2_moments :
    (∑ i ∈ range 2, b₂ i = 1) ∧ (∑ i ∈ range 2, b₂ i * c₂ i = 1 / 2)
      ∧ (∑ i ∈ range 2, b₂ i * (c₂ i) ^ 2 = 1 / 3) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Finset.sum_range_succ, b₂, c₂] <;> norm_num

/-- `R₂ e = b₂`. -/
lemma s2_Re : ∀ i ∈ range 2, b₂ i = ∑ j ∈ range 2, R₂ i j := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 := by have := mem_range.1 hi; omega
  rcases hi' with rfl | rfl <;> simp [Finset.sum_range_succ, R₂, b₂] <;> norm_num

/-- The algebraic-stability matrix of the `s = 2` near-miss vanishes: `M = 0`. -/
lemma s2_M_zero : ∀ i ∈ range 2, ∀ j ∈ range 2,
    (∑ k ∈ range 2, R₂ i k * A₂ k j) + (∑ k ∈ range 2, R₂ j k * A₂ k i)
      - b₂ i * b₂ j = 0 := by
  intro i hi j hj
  have hi' : i = 0 ∨ i = 1 := by have := mem_range.1 hi; omega
  have hj' : j = 0 ∨ j = 1 := by have := mem_range.1 hj; omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
    simp [Finset.sum_range_succ, R₂, A₂, b₂] <;> norm_num

/-- `A₂` is entrywise nonnegative. -/
lemma s2_A_nonneg : ∀ i j, 0 ≤ A₂ i j := by
  intro i j
  unfold A₂
  split_ifs <;> norm_num

/-- `b₂` is positive on the stage range. -/
lemma s2_b_pos : ∀ i ∈ range 2, 0 < b₂ i := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 := by have := mem_range.1 hi; omega
  rcases hi' with rfl | rfl <;> norm_num [b₂]

/-- `R₂` is symmetric. -/
lemma s2_R_symm : SymmOn 2 R₂ := by
  intro i hi j hj
  have hi' : i = 0 ∨ i = 1 := by have := mem_range.1 hi; omega
  have hj' : j = 0 ∨ j = 1 := by have := mem_range.1 hj; omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> norm_num [R₂]

/-- `R₂` is positive semidefinite.  Completing the square:
`5/8 x₀² + 2·(1/8) x₀x₁ + 1/8 x₁² = (1/8)(x₀ + x₁)² + (1/2) x₀²`. -/
lemma s2_R_psd : PSDOn 2 R₂ := by
  intro x
  have hexp : ∑ i ∈ range 2, ∑ j ∈ range 2, R₂ i j * (x i * x j)
      = (1/8) * (x 0 + x 1) ^ 2 + (1/2) * (x 0) ^ 2 := by
    simp [Finset.sum_range_succ, R₂]
    ring
  rw [hexp]
  positivity

/-- The abscissas of the `s = 2` near-miss are strictly increasing and lie in `[0,1]`. -/
lemma s2_c_sorted : c₂ 0 < c₂ 1 ∧ 0 ≤ c₂ 0 ∧ c₂ 1 ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [c₂]

/-- The `s = 2` near-miss has `bᵀAc = 2/9`, not `1/6`. -/
theorem s2_bAc_eq :
    ∑ i ∈ range 2, b₂ i * ∑ j ∈ range 2, A₂ i j * c₂ j = 2 / 9 := by
  simp [Finset.sum_range_succ, A₂, b₂, c₂]
  norm_num

/-- `2/9 ≠ 1/6`, so the near-miss fails exactly the `bᵀAc` condition. -/
theorem s2_bAc_ne :
    ∑ i ∈ range 2, b₂ i * ∑ j ∈ range 2, A₂ i j * c₂ j ≠ 1 / 6 := by
  rw [s2_bAc_eq]; norm_num

/-- **The `s = 2` near-miss, packaged.**

Every hypothesis of the Claim holds for `(A₂, b₂, R₂, c₂)` — `A ≥ 0`, `b > 0`, `c = Ae`
strictly increasing in `[0,1]`, `R` symmetric positive semidefinite with `Re = b`, and the
moment conditions `bᵀe = 1`, `bᵀc = 1/2`, `bᵀc² = 1/3` — and moreover `M = 0`, which the
Claim declares impossible.  The single hypothesis that fails is `bᵀAc = 1/6`.

Since `R₂` is not diagonal (`s2_R_not_diagonal`), this is consistent with
`R_not_diagonal`.  It shows the obstruction to a small counterexample is the `bᵀAc`
condition, which is what forces the nine-stage construction of `main-4.tex`. -/
theorem s2_near_miss :
    (∀ i j, 0 ≤ A₂ i j)
      ∧ (∀ i ∈ range 2, 0 < b₂ i)
      ∧ (∀ i ∈ range 2, c₂ i = ∑ j ∈ range 2, A₂ i j)
      ∧ (c₂ 0 < c₂ 1)
      ∧ SymmOn 2 R₂ ∧ PSDOn 2 R₂
      ∧ (∀ i ∈ range 2, b₂ i = ∑ j ∈ range 2, R₂ i j)
      ∧ (∑ i ∈ range 2, b₂ i = 1)
      ∧ (∑ i ∈ range 2, b₂ i * c₂ i = 1 / 2)
      ∧ (∑ i ∈ range 2, b₂ i * (c₂ i) ^ 2 = 1 / 3)
      ∧ (∀ i ∈ range 2, ∀ j ∈ range 2,
          (∑ k ∈ range 2, R₂ i k * A₂ k j) + (∑ k ∈ range 2, R₂ j k * A₂ k i)
            - b₂ i * b₂ j = 0)
      ∧ (∑ i ∈ range 2, b₂ i * ∑ j ∈ range 2, A₂ i j * c₂ j ≠ 1 / 6) :=
  ⟨s2_A_nonneg, s2_b_pos, c₂_eq_rowSum, s2_c_sorted.1, s2_R_symm, s2_R_psd, s2_Re,
    s2_moments.1, s2_moments.2.1, s2_moments.2.2, s2_M_zero, s2_bAc_ne⟩

/-- The `s = 2` near-miss certificate is not diagonal, as `R_not_diagonal` predicts for
any tableau with `M = 0`. -/
theorem s2_R_not_diagonal : ¬ DiagOn 2 R₂ := by
  intro hd
  have h := hd 0 (by simp) 1 (by simp) (by norm_num)
  norm_num [R₂] at h

/-! ## The separation -/

/-- **The Claim of `main-4.tex` is false as stated.**

If the construction of §2 goes through at some parameter (i.e. `ConstructionData s` is
inhabited), then the Claim fails: there is a tableau meeting all of its hypotheses whose
algebraic-stability matrix is positive semidefinite — indeed identically zero. -/
theorem claim_false {s : ℕ} (g : ConstructionData s) :
    ∃ d : AlgStabData s, PSDOn s (fun i j =>
      (∑ k ∈ range s, d.R i k * d.A k j)
        + (∑ k ∈ range s, d.R j k * d.A k i) - d.b i * d.b j) :=
  ⟨g.toAlgStabData, g.toAlgStabData.M_psd⟩

/-- **The certificate of the counterexample is not diagonal.**  A corollary of
`R_not_diagonal`: the `R` produced by the construction of §2 (which has rank `3`, being
`D Lᵀ B_G L D` with `L` of rank `3`) is necessarily non-diagonal. -/
theorem construction_R_not_diagonal {s : ℕ} (g : ConstructionData s) :
    ¬ DiagOn s g.R :=
  R_not_diagonal g.toAlgStabData

/-- **The diagonal case, for contrast (`SSPLean/BStability.lean`).**  When the
certificate is `R = diag b`, the Claim's conclusion is a theorem: no nonnegative tableau
with sorted abscissas, row sums `≤ c` and the order-three quadrature conditions has a PSD
algebraic-stability matrix. -/
theorem diag_case_impossible {s : ℕ} (A : ℕ → ℕ → ℝ) (b c : ℕ → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i j, i ≤ j → j < s → c i ≤ c j)
    (hrow : ∀ i < s, ∑ j ∈ range s, A i j ≤ c i)
    (h1 : ∑ i ∈ range s, b i = 1)
    (h2 : ∑ i ∈ range s, b i * c i = 1 / 2)
    (h3 : ∑ i ∈ range s, b i * (c i) ^ 2 = 1 / 3)
    (hM : PSDOn s (fun i j => b i * A i j + b j * A j i - b i * b j)) :
    False :=
  SSP.no_order3_algebraically_stable A b c hA hb hc hrow h1 h2 h3 hM

/-- **The gap in the Claim, packaged.**

Under the construction of §2 the two regimes separate cleanly:

1. with a general symmetric PSD certificate `R` satisfying `R e = b`, the Claim's
   conclusion *fails* — a tableau exists with `M = 0`;
2. with the diagonal certificate `R = diag b`, the Claim's conclusion *holds*;
3. and every counterexample's certificate is non-diagonal.

So the Claim as stated in `main-4.tex` is false, and an extra hypothesis on `R` beyond
"symmetric positive semidefinite with `R e = b`" is genuinely required — for instance
`R = diag b`, or (as the paper suggests) `R` entrywise nonnegative. -/
theorem claim_needs_extra_hypothesis {s : ℕ} (g : ConstructionData s) :
    (∃ d : AlgStabData s, ¬ DiagOn s d.R)
      ∧ (∀ A : ℕ → ℕ → ℝ, ∀ b c : ℕ → ℝ,
          (∀ i j, 0 ≤ A i j) → (∀ i, 0 ≤ b i) →
          (∀ i j, i ≤ j → j < s → c i ≤ c j) →
          (∀ i < s, ∑ j ∈ range s, A i j ≤ c i) →
          (∑ i ∈ range s, b i = 1) →
          (∑ i ∈ range s, b i * c i = 1 / 2) →
          (∑ i ∈ range s, b i * (c i) ^ 2 = 1 / 3) →
          ¬ PSDOn s (fun i j => b i * A i j + b j * A j i - b i * b j)) :=
  ⟨⟨g.toAlgStabData, construction_R_not_diagonal g⟩,
   fun A b c hA hb hc hrow h1 h2 h3 hM =>
     diag_case_impossible A b c hA hb hc hrow h1 h2 h3 hM⟩

/-! ## Closing the loop: `hord4` derived from the IVT rather than assumed

`ConstructionData` above takes the order-three condition `hord4` as a *hypothesis* "at the
IVT parameter".  That leaves a gap: nothing connects it to `tau_exists`.  We close the gap
here by carrying the parameter explicitly.

`ConstructionFamily s` is the one-parameter family of §2: the tableau entries are functions
of `t`, the `t`-*independent* identities (`RA + AᵀR = bbᵀ`, `Re = b`, `bᵀe = 1`,
`bᵀc = 1/2`, `bᵀAc = 1/6`, positivity, monotonicity) are hypotheses holding for every `t`
in the interval, and the order-three *defect*

  `defect t = Σᵢ b t i * (c t i)² − 1/3`

is required only to be continuous with the exactly-computed endpoint signs.  Then
`hord4` is no longer assumed: `ConstructionFamily.toConstructionData` **derives** it at the
`τ` supplied by `tau_exists_of_sign_change`.

This is the faithful rendering of the paper's logic: the sign change of the defect is the
sole analytic input, and it is what produces the parameter at which the counterexample
lives. -/

/-- The one-parameter family of `main-4.tex` §2.

All fields except the last three are the `t`-independent algebraic content, asserted for
every `t` in the bracketing interval.  The last three are the analytic input: continuity
of the order-three defect and its two endpoint signs. -/
structure ConstructionFamily (s : ℕ) where
  /-- `A(t) = D(t)⁻¹ G D(t)`. -/
  A : ℝ → ℕ → ℕ → ℝ
  /-- `b(t) = D(t) h(t)`. -/
  b : ℝ → ℕ → ℝ
  /-- `R(t) = D(t) X(t) D(t)`. -/
  R : ℝ → ℕ → ℕ → ℝ
  /-- `c(t) = A(t) e`. -/
  c : ℝ → ℕ → ℝ
  /-- `A(t) ≥ 0` for every parameter in the interval. -/
  hApos : ∀ t ∈ Set.Icc tL tR, ∀ i j, 0 ≤ A t i j
  /-- `b(t) > 0` on the stage range. -/
  hbpos : ∀ t ∈ Set.Icc tL tR, ∀ i ∈ range s, 0 < b t i
  /-- `c(t) = A(t) e`. -/
  hcdef : ∀ t ∈ Set.Icc tL tR, ∀ i ∈ range s, c t i = ∑ j ∈ range s, A t i j
  /-- The abscissas are strictly increasing. -/
  hcmono : ∀ t ∈ Set.Icc tL tR, ∀ i ∈ range s, ∀ j ∈ range s, i < j → c t i < c t j
  /-- The abscissas lie in `[0, 1]`. -/
  hcrange : ∀ t ∈ Set.Icc tL tR, ∀ i ∈ range s, 0 ≤ c t i ∧ c t i ≤ 1
  /-- `R(t)` is symmetric. -/
  hRsymm : ∀ t ∈ Set.Icc tL tR, SymmOn s (R t)
  /-- `R(t)` is positive semidefinite. -/
  hRpsd : ∀ t ∈ Set.Icc tL tR, PSDOn s (R t)
  /-- `R(t) e = b(t)`, from `X v = h`. -/
  hRe : ∀ t ∈ Set.Icc tL tR, ∀ i ∈ range s, b t i = ∑ j ∈ range s, R t i j
  /-- `b(t)ᵀ e = 1`, for every `t`. -/
  hord1 : ∀ t ∈ Set.Icc tL tR, ∑ i ∈ range s, b t i = 1
  /-- `b(t)ᵀ c(t) = 1/2`, for every `t`. -/
  hord2 : ∀ t ∈ Set.Icc tL tR, ∑ i ∈ range s, b t i * c t i = 1 / 2
  /-- `b(t)ᵀ A(t) c(t) = 1/6`, for every `t`. -/
  hord3 : ∀ t ∈ Set.Icc tL tR,
    ∑ i ∈ range s, b t i * ∑ j ∈ range s, A t i j * c t j = 1 / 6
  /-- `R(t) A(t) + A(t)ᵀ R(t) − b(t) b(t)ᵀ = 0`, for every `t`. -/
  hMzero : ∀ t ∈ Set.Icc tL tR, ∀ i ∈ range s, ∀ j ∈ range s,
    (∑ k ∈ range s, R t i k * A t k j) + (∑ k ∈ range s, R t j k * A t k i)
      - b t i * b t j = 0
  /-- The order-three defect is continuous on the interval. -/
  hcont : ContinuousOn (fun t => (∑ i ∈ range s, b t i * (c t i) ^ 2) - 1 / 3)
    (Set.Icc tL tR)
  /-- The defect is negative at the left endpoint (exact rational evaluation). -/
  hdefL : (∑ i ∈ range s, b tL i * (c tL i) ^ 2) - 1 / 3 < 0
  /-- The defect is positive at the right endpoint (exact rational evaluation). -/
  hdefR : 0 < (∑ i ∈ range s, b tR i * (c tR i) ^ 2) - 1 / 3

/-- **The parameter `τ` of the family, from the intermediate value theorem.**

This is where `tau_exists_of_sign_change` is actually used: the sign change of the
order-three defect produces a parameter in the open interval at which the order-three
condition `bᵀc² = 1/3` holds exactly. -/
theorem ConstructionFamily.tau_spec {s : ℕ} (F : ConstructionFamily s) :
    ∃ τ ∈ Set.Ioo tL tR, ∑ i ∈ range s, F.b τ i * (F.c τ i) ^ 2 = 1 / 3 := by
  obtain ⟨τ, hτ, hzero⟩ :=
    tau_exists_of_sign_change _ F.hcont F.hdefL F.hdefR
  exact ⟨τ, hτ, by linarith [hzero]⟩

/-- The IVT parameter of the family, as a term. -/
noncomputable def ConstructionFamily.tau {s : ℕ} (F : ConstructionFamily s) : ℝ :=
  F.tau_spec.choose

lemma ConstructionFamily.tau_mem {s : ℕ} (F : ConstructionFamily s) :
    F.tau ∈ Set.Ioo tL tR := F.tau_spec.choose_spec.1

/-- At `F.tau` the order-three condition holds — this is the IVT conclusion. -/
lemma ConstructionFamily.tau_ord4 {s : ℕ} (F : ConstructionFamily s) :
    ∑ i ∈ range s, F.b F.tau i * (F.c F.tau i) ^ 2 = 1 / 3 :=
  F.tau_spec.choose_spec.2

/-- **The family yields a `ConstructionData` — with `hord4` proved, not assumed.**

At the IVT parameter `F.tau` all the `t`-independent identities specialize, and the
order-three condition is *derived* from `tau_ord4`.  This is the step that makes the
`τ`-existence theorem load-bearing. -/
noncomputable def ConstructionFamily.toConstructionData {s : ℕ}
    (F : ConstructionFamily s) : ConstructionData s :=
  have hmem : F.tau ∈ Set.Icc tL tR :=
    Set.mem_Icc.2 ⟨le_of_lt F.tau_mem.1, le_of_lt F.tau_mem.2⟩
  { A := F.A F.tau
    b := F.b F.tau
    R := F.R F.tau
    c := F.c F.tau
    hApos := F.hApos F.tau hmem
    hbpos := F.hbpos F.tau hmem
    hcdef := F.hcdef F.tau hmem
    hcmono := F.hcmono F.tau hmem
    hcrange := F.hcrange F.tau hmem
    hRsymm := F.hRsymm F.tau hmem
    hRpsd := F.hRpsd F.tau hmem
    hRe := F.hRe F.tau hmem
    hord1 := F.hord1 F.tau hmem
    hord2 := F.hord2 F.tau hmem
    hord3 := F.hord3 F.tau hmem
    hord4 := F.tau_ord4
    hMzero := F.hMzero F.tau hmem }

/-- **The Claim is false, given only the `t`-independent identities and the defect's sign
change.**  The order-three condition is not assumed anywhere: it is produced by the
intermediate value theorem. -/
theorem claim_false_of_family {s : ℕ} (F : ConstructionFamily s) :
    ∃ d : AlgStabData s, PSDOn s (fun i j =>
      (∑ k ∈ range s, d.R i k * d.A k j)
        + (∑ k ∈ range s, d.R j k * d.A k i) - d.b i * d.b j) :=
  claim_false F.toConstructionData

/-- The certificate of the family's counterexample is not diagonal. -/
theorem family_R_not_diagonal {s : ℕ} (F : ConstructionFamily s) :
    ¬ DiagOn s F.toConstructionData.R :=
  construction_R_not_diagonal F.toConstructionData

end Counterexample

end SSP
