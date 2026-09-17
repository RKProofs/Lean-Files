import SSPLean.ThreeStageClaim

/-!
# The Claim is inconsistent at two stages

This file proves the `s = 2` analogue of `SSPLean.ThreeStageClaim`: there is no two-stage
tableau `A ≥ 0` together with a symmetric positive semidefinite `R` satisfying `Re = b`,
`b ≥ 0`, `c = Ae`, `M = RA + AᵗR − bbᵗ ⪰ 0`, and the order conditions

  `bᵗe = 1`,   `bᵗc = 1/2`,   `bᵗc² = 1/3`,   `bᵗAc = 1/6`.

As at three stages, no sign condition on `R`, no distinctness of the `cᵢ`, no upper bound on
`c`, and no strict positivity of `b` is assumed.

## The argument

Write `b = (p, q)`.  The first three order conditions give the variance identity

  `pq(c₁ − c₂)² = bᵗc² − (bᵗc)² = 1/3 − 1/4 = 1/12`,

which already forces `p, q > 0` and `c₁ ≠ c₂` (`bvar`, `bpos`, `cne`).  Eliminating `p` and `q`
via `p_eq`, `q_eq` gives the single constraint on the abscissae

  `(c₂ − 1/2)(1/2 − c₁) = 1/12`   (`ckey`).

Next, `eᵗMe = 2bᵗc − (bᵗe)² = 0` and `M ⪰ 0` force `Me = 0`, i.e. `Rc + Aᵗb = b` (`Rc_eq2`).
All four order conditions then pin `(Aᵗb)₁ = p(1 − c₁)` (`ATb_fst`).  At two stages this
determines `R` completely: every symmetric `R` with `Re = b` has the form
`R = ⟨r, p−r; p−r, q−p+r⟩`, and comparing first components of `Rc` gives
`r(c₂−c₁) = p(c₂−c₁)`, hence **`R = diag(p, q)`** (`Rdiag`).  *This is the step with no
three-stage analogue* — at `s = 3` the conditions `Re = b` and `Rc = b − Aᵗb` leave `R`
genuinely free, which is why `ThreeStageClaim` needs the whole quotient/accretivity apparatus.

With `R` diagonal, the `i`-th diagonal entry of `M` is `2bᵢAᵢᵢ − bᵢ²`, so `M ⪰ 0` gives
`Aᵢᵢ ≥ bᵢ/2`, while `A ≥ 0` and `cᵢ = Σⱼ Aᵢⱼ` give `Aᵢᵢ ≤ cᵢ`.  For the index carrying the
*smaller* `c` — say `c₁ < c₂` — `ckey` yields

  `2(c₂ − c₁)(c₁ − p/2) = −(12c₁² − 6c₁ + 1)/6 < 0`,

the numerator having discriminant `−12`.  So `p/2 ≤ A₁₁ ≤ c₁ < p/2` — impossible.

The source note reaches this by relabelling so that `c₁ < c₂`.  Since the whole setup is
symmetric in the two stages, we instead prove both branches (`c_lt_half_b_fst` and
`c_lt_half_b_snd`) and dispatch on `lt_trichotomy`, which avoids developing any relabelling
machinery.  Note also that the note's `α, β > 0` is a genuine consequence rather than a
convention: `p, q > 0` and `p + q = 1` force `α` and `β` to share the sign of `α + β = c₂ − c₁`.

## Main results

* `two_stage_claim_inconsistent` : `¬ Nonempty Data2`
* `no_two_stage_tableau` : the same with the tableau supplied as explicit arguments
* `Rdiag` : the two-stage rigidity `R = diag b`, of independent interest — allowing a full
  matrix `R` gives no extra freedom at two stages

Everything is machine-checked, with no `sorry` and no axioms beyond `propext`,
`Classical.choice`, and `Quot.sound`.  Only `SSP.ThreeStage.psd_kernel` is reused from the
three-stage development (it is stated for a general `range n`).
-/

open Finset

namespace SSP.TwoStage

/-- The two-stage hypotheses of the Claim, bundled.  Mirrors `SSP.ThreeStage.Data` with
`range 3` replaced by `range 2`. -/
structure Data2 where
  A : ℕ → ℕ → ℝ
  R : ℕ → ℕ → ℝ
  b : ℕ → ℝ
  c : ℕ → ℝ
  hA : ∀ i ∈ range 2, ∀ j ∈ range 2, 0 ≤ A i j
  hRsymm : ∀ i ∈ range 2, ∀ j ∈ range 2, R i j = R j i
  hRpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 2, ∑ j ∈ range 2, R i j * (x i * x j)
  hb : ∀ i ∈ range 2, b i = ∑ j ∈ range 2, R i j
  hbnn : ∀ i ∈ range 2, 0 ≤ b i
  hc : ∀ i ∈ range 2, c i = ∑ j ∈ range 2, A i j
  hMpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 2, ∑ j ∈ range 2,
    ((∑ k ∈ range 2, R i k * A k j) + (∑ k ∈ range 2, R j k * A k i) - b i * b j) * (x i * x j)
  h1 : ∑ i ∈ range 2, b i = 1
  h2 : ∑ i ∈ range 2, b i * c i = 1/2
  h3 : ∑ i ∈ range 2, b i * (c i)^2 = 1/3
  h4 : ∑ i ∈ range 2, b i * ∑ j ∈ range 2, A i j * c j = 1/6

variable (d : Data2)

/-- Expand a two-term sum. -/
lemma sum2 (f : ℕ → ℝ) : ∑ i ∈ range 2, f i = f 0 + f 1 := by
  simp only [show (2:ℕ)=1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-! ## The weights and the abscissae -/

/-- **The variance identity `pq(c₁−c₂)² = 1/12`.**  Immediate from
`bᵗc² − (bᵗc)² = 1/3 − 1/4` together with `bᵗe = 1`. -/
lemma bvar : d.b 0 * d.b 1 * (d.c 0 - d.c 1)^2 = 1/12 := by
  have h1 := d.h1; have h2 := d.h2; have h3 := d.h3
  rw [sum2] at h1 h2 h3
  linear_combination (1/3 : ℝ)*h1
    + (-(d.c 0)*(d.b 0) - (d.c 1)*(d.b 1) - 1/2)*h2 + (d.b 0 + d.b 1)*h3

/-- **Both weights are strictly positive.**  If either vanished the variance would too. -/
lemma bpos : 0 < d.b 0 ∧ 0 < d.b 1 := by
  have hv := bvar d
  have n0 := d.hbnn 0 (by simp)
  have n1 := d.hbnn 1 (by simp)
  constructor
  · rcases eq_or_lt_of_le n0 with h | h
    · exfalso; rw [← h] at hv; norm_num at hv
    · exact h
  · rcases eq_or_lt_of_le n1 with h | h
    · exfalso; rw [← h] at hv; norm_num at hv
    · exact h

/-- **The abscissae are distinct.** -/
lemma cne : d.c 0 ≠ d.c 1 := by
  intro h
  have hv := bvar d
  rw [h] at hv
  norm_num at hv

/-- `p·(c₂ − c₁) = c₂ − 1/2`, from `bᵗe = 1` and `bᵗc = 1/2`. -/
lemma p_eq : d.b 0 * (d.c 1 - d.c 0) = d.c 1 - 1/2 := by
  have h1 := d.h1; have h2 := d.h2
  rw [sum2] at h1 h2
  linear_combination (d.c 1)*h1 - h2

/-- `q·(c₂ − c₁) = 1/2 − c₁`. -/
lemma q_eq : d.b 1 * (d.c 1 - d.c 0) = 1/2 - d.c 0 := by
  have h1 := d.h1; have h2 := d.h2
  rw [sum2] at h1 h2
  linear_combination (-(d.c 0))*h1 + h2

/-- **The constraint on the abscissae alone**: `(c₂ − 1/2)(1/2 − c₁) = 1/12`.  This is `bvar`
with `p` and `q` eliminated via `p_eq` and `q_eq`. -/
lemma ckey : (d.c 1 - 1/2) * (1/2 - d.c 0) = 1/12 := by
  have hv := bvar d
  have hp := p_eq d
  have hq := q_eq d
  linear_combination hv - (1/2 - d.c 0)*hp - (d.b 0 * (d.c 1 - d.c 0))*hq

/-! ## `M e = 0`, and the two-stage rigidity of `R` -/

/-- `M` is symmetric. -/
lemma Msymm2 : ∀ i ∈ range 2, ∀ j ∈ range 2,
    ((∑ k ∈ range 2, d.R i k * d.A k j) + (∑ k ∈ range 2, d.R j k * d.A k i) - d.b i * d.b j)
    = ((∑ k ∈ range 2, d.R j k * d.A k i) + (∑ k ∈ range 2, d.R i k * d.A k j)
        - d.b j * d.b i) := by
  intro i _ j _; ring

/-- Column sums of `R` are `b`, by symmetry. -/
lemma Rcol2 (k : ℕ) (hk : k ∈ range 2) : d.R 0 k + d.R 1 k = d.b k := by
  have hb := d.hb k hk
  rw [sum2] at hb
  have hk' := mem_range.1 hk
  interval_cases k
  · rw [d.hRsymm 1 (by simp) 0 (by simp)]; linarith
  · rw [d.hRsymm 0 (by simp) 1 (by simp)]; linarith

/-- **`eᵗMe = 0`**, since `Ae = c`, `Re = b`, `bᵗe = 1` and `bᵗc = 1/2`. -/
lemma eMe_zero2 : ∑ i ∈ range 2, ∑ j ∈ range 2,
    ((∑ k ∈ range 2, d.R i k * d.A k j) + (∑ k ∈ range 2, d.R j k * d.A k i)
      - d.b i * d.b j) * ((fun _ => (1:ℝ)) i * (fun _ => (1:ℝ)) j) = 0 := by
  have k0 := Rcol2 d 0 (by simp); have k1 := Rcol2 d 1 (by simp)
  have c0 := d.hc 0 (by simp); have c1 := d.hc 1 (by simp)
  rw [sum2] at c0 c1
  have h1 := d.h1; have h2 := d.h2
  rw [sum2] at h1 h2
  simp only [show (2:ℕ)=1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  linear_combination
    (-(d.R 0 1) - (d.R 1 1) + (d.b 0) + 2*(d.b 1) + 2*(d.c 0) - 1)*k0
    + ((d.R 0 0) + (d.R 1 0) + (d.b 1) + 2*(d.c 1) - 1)*k1
    + (-2*(d.R 0 0) - 2*(d.R 1 0))*c0 + (-2*(d.R 0 1) - 2*(d.R 1 1))*c1
    + (-(d.R 0 0) - (d.R 0 1) - (d.R 1 0) - (d.R 1 1) - 1)*h1 + 2*h2

/-- **`Me = 0`**: the psd form `M` vanishes at `e`, so `e` is in its kernel. -/
lemma Me_zero2 (z : ℕ → ℝ) : ∑ i ∈ range 2, ∑ j ∈ range 2,
    ((∑ k ∈ range 2, d.R i k * d.A k j) + (∑ k ∈ range 2, d.R j k * d.A k i)
      - d.b i * d.b j) * ((fun _ => (1:ℝ)) i * z j) = 0 :=
  SSP.ThreeStage.psd_kernel _ (Msymm2 d) d.hMpsd (fun _ => 1) (eMe_zero2 d) z

/-- **`Rc + Aᵗb = b`, coordinatewise** — the kernel identity, read off from `Me_zero2` at the
coordinate vectors. -/
lemma Rc_eq2 (j : ℕ) (hj : j ∈ range 2) :
    (∑ k ∈ range 2, d.R j k * d.c k) + (∑ i ∈ range 2, d.A i j * d.b i) = d.b j := by
  have h := Me_zero2 d (fun k => if k = j then 1 else 0)
  have hj' := mem_range.1 hj
  have k0 := Rcol2 d 0 (by simp); have k1 := Rcol2 d 1 (by simp)
  have c0 := d.hc 0 (by simp); have c1 := d.hc 1 (by simp)
  rw [sum2] at c0 c1
  have h1 := d.h1
  rw [sum2] at h1
  simp only [show (2:ℕ)=1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at h ⊢
  interval_cases j
  · norm_num at h
    rw [d.hRsymm 0 (by simp) 1 (by simp)] at *
    linear_combination h + (-(d.A 0 0) - (d.b 0) - (d.b 1) + 1)*k0 + (-(d.A 1 0))*k1
      + (d.R 0 0)*c0 + (d.R 1 0)*c1 + ((d.R 0 0) + (d.R 1 0))*h1
  · norm_num at h
    rw [d.hRsymm 0 (by simp) 1 (by simp)] at *
    linear_combination h
      + (-(d.A 0 1) + (d.R 1 0) + (d.R 1 1) - (d.b 1))*k0
      + (-(d.A 1 1) - (d.R 0 0) - (d.R 1 0) - (d.b 1) + 1)*k1
      + (d.R 1 0)*c0 + (d.R 1 1)*c1 + ((d.R 1 0) + (d.R 1 1))*h1

/-- **`(Aᵗb)₁ = p(1 − c₁)`** — step (3) of the note.  Uses all four order conditions: with
`bᵗe = 1` and `bᵗc = 1/2` one has `bᵗAc = c₂/2 + (c₁−c₂)(Aᵗb)₁`, and `bᵗAc = 1/6` together with
`bᵗc² = 1/3` pins the value. -/
lemma ATb_fst : d.A 0 0 * d.b 0 + d.A 1 0 * d.b 1 = d.b 0 * (1 - d.c 0) := by
  have h1 := d.h1; have h2 := d.h2; have h3 := d.h3; have h4 := d.h4
  rw [sum2] at h1 h2 h3
  have c0 := d.hc 0 (by simp); have c1 := d.hc 1 (by simp)
  rw [sum2] at c0 c1
  simp only [show (2:ℕ)=1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at h4
  have hd : d.c 1 - d.c 0 ≠ 0 := fun h => cne d (by linarith)
  have hexp : (d.c 1 - d.c 0)
      * ((d.A 0 0 * d.b 0 + d.A 1 0 * d.b 1) - d.b 0 * (1 - d.c 0)) = 0 := by
    linear_combination (-(d.c 1))*h1 + ((d.A 1 0) + (d.A 1 1) + (d.c 1) + 1)*h2 - h3 - h4
      + (-(d.A 1 0)*(d.b 0) - (d.A 1 1)*(d.b 0))*c0
      + ((d.A 0 0)*(d.b 0) + (d.A 0 1)*(d.b 0) - 1/2)*c1
  rcases mul_eq_zero.mp hexp with h | h
  · exact absurd h hd
  · linarith

/-- **`(Aᵗb)₂ = q(1 − c₂)`** — the mirror of `ATb_fst`. -/
lemma ATb_snd : d.A 0 1 * d.b 0 + d.A 1 1 * d.b 1 = d.b 1 * (1 - d.c 1) := by
  have h1 := d.h1; have h2 := d.h2; have h3 := d.h3; have h4 := d.h4
  rw [sum2] at h1 h2 h3
  have c0 := d.hc 0 (by simp); have c1 := d.hc 1 (by simp)
  rw [sum2] at c0 c1
  simp only [show (2:ℕ)=1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at h4
  have hd : d.c 0 - d.c 1 ≠ 0 := fun h => cne d (by linarith)
  have hexp : (d.c 0 - d.c 1)
      * ((d.A 0 1 * d.b 0 + d.A 1 1 * d.b 1) - d.b 1 * (1 - d.c 1)) = 0 := by
    linear_combination
      (-(d.A 0 0)*(d.c 1) - (d.A 0 1)*(d.c 1) + (d.A 1 0)*(d.c 0) + (d.A 1 1)*(d.c 0)
        - (d.c 0))*h1
      + ((d.A 0 0) + (d.A 0 1) + (d.c 0) + 1)*h2 - h3 - h4
      + (-(d.A 1 0)*(d.b 0) + (d.A 1 0) - (d.A 1 1)*(d.b 0) + (d.A 1 1) - 1/2)*c0
      + ((d.A 0 0)*(d.b 0) - (d.A 0 0) + (d.A 0 1)*(d.b 0) - (d.A 0 1))*c1
  rcases mul_eq_zero.mp hexp with h | h
  · exact absurd h hd
  · linarith

/-- **The two-stage rigidity: `R = diag b`.**

A symmetric `R` with `Re = b` is `⟨r, p−r; p−r, q−p+r⟩` for `r = R₁₁`.  The first component of
`Rc` is then `pc₂ − r(c₂−c₁)`, while `Rc + Aᵗb = b` and `(Aᵗb)₁ = p(1−c₁)` give `(Rc)₁ = pc₁`.
Since `c₁ ≠ c₂` this forces `r = p`, hence `R₁₂ = R₂₁ = 0` and `R₂₂ = q`.

**No three-stage analogue.**  At `s = 3` the conditions `Re = b` and `Rc = b − Aᵗb` are two
linear constraints on a six-dimensional space of symmetric matrices, so `R` stays free; that is
exactly why `ThreeStageClaim` needs the quotient and accretivity machinery. -/
lemma Rdiag : d.R 0 0 = d.b 0 ∧ d.R 0 1 = 0 ∧ d.R 1 0 = 0 ∧ d.R 1 1 = d.b 1 := by
  have hr := Rc_eq2 d 0 (by simp)
  have hT := ATb_fst d
  have h1 := d.h1; have h2 := d.h2
  rw [sum2] at h1 h2
  have k0 := Rcol2 d 0 (by simp)
  have c0 := d.hc 0 (by simp); have c1 := d.hc 1 (by simp)
  rw [sum2] at c0 c1
  have hs := d.hRsymm 0 (by simp) 1 (by simp)
  simp only [show (2:ℕ)=1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at hr
  norm_num at hr
  have hrp : (d.c 1 - d.c 0) * (d.R 0 0 - d.b 0) = 0 := by
    linear_combination (d.c 1)*k0 + ((d.R 0 1) - (d.R 1 0))*c1
      + ((d.A 1 0) + (d.A 1 1))*hs - hr + hT
  have hd : d.c 1 - d.c 0 ≠ 0 := fun h => cne d (by linarith)
  have hr00 : d.R 0 0 = d.b 0 := by
    rcases mul_eq_zero.mp hrp with h | h
    · exact absurd h hd
    · linarith
  have hb0 := d.hb 0 (by simp)
  rw [sum2] at hb0
  have hr01 : d.R 0 1 = 0 := by rw [hr00] at hb0; linarith
  have hr10 : d.R 1 0 = 0 := by rw [← hs]; exact hr01
  have hb1 := d.hb 1 (by simp)
  rw [sum2] at hb1
  have hr11 : d.R 1 1 = d.b 1 := by rw [hr10] at hb1; linarith
  exact ⟨hr00, hr01, hr10, hr11⟩

/-! ## The contradiction

The setup is symmetric in the two stages, so rather than relabel we run the same argument at
whichever index carries the *smaller* `c`.  For that index `i`, `M ⪰ 0` forces
`Aᵢᵢ ≥ bᵢ/2` (the diagonal entry of `M` is `2bᵢAᵢᵢ − bᵢ²` once `R = diag b`), while `A ≥ 0`
and `cᵢ = Σⱼ Aᵢⱼ` force `Aᵢᵢ ≤ cᵢ`; and the constraint on the abscissae forces `cᵢ < bᵢ/2`. -/

/-- **`A₁₁ ≥ p/2`**, from the first diagonal entry `M₁₁ = 2pA₁₁ − p²` of the psd matrix `M`. -/
lemma diag_lower_fst : d.b 0 / 2 ≤ d.A 0 0 := by
  obtain ⟨r00, r01, _, _⟩ := Rdiag d
  have hM := d.hMpsd (fun i => if i = 0 then 1 else 0)
  simp only [show (2:ℕ)=1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at hM
  norm_num at hM
  rw [r00, r01] at hM
  have hp := (bpos d).1
  nlinarith [hM, hp]

/-- **`A₂₂ ≥ q/2`**, the mirror of `diag_lower_fst`. -/
lemma diag_lower_snd : d.b 1 / 2 ≤ d.A 1 1 := by
  obtain ⟨_, _, r10, r11⟩ := Rdiag d
  have hM := d.hMpsd (fun i => if i = 1 then 1 else 0)
  simp only [show (2:ℕ)=1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero] at hM
  norm_num at hM
  rw [r10, r11] at hM
  have hq := (bpos d).2
  nlinarith [hM, hq]

/-- **`A₁₁ ≤ c₁`**, since `c₁ = A₁₁ + A₁₂` and `A₁₂ ≥ 0`. -/
lemma diag_upper_fst : d.A 0 0 ≤ d.c 0 := by
  have hc := d.hc 0 (by simp)
  rw [sum2] at hc
  have h := d.hA 0 (by simp) 1 (by simp)
  linarith

/-- **`A₂₂ ≤ c₂`**. -/
lemma diag_upper_snd : d.A 1 1 ≤ d.c 1 := by
  have hc := d.hc 1 (by simp)
  rw [sum2] at hc
  have h := d.hA 1 (by simp) 0 (by simp)
  linarith

/-- **The numerical obstruction at the smaller index.**  If `c₁ < c₂` then

  `2(c₂ − c₁)(c₁ − p/2) = −(12c₁² − 6c₁ + 1)/6 < 0`,

the numerator having discriminant `−12`.  Hence `c₁ < p/2`.  (The same quantity
`12c₁² − 6c₁ + 1` appears in `SSP.ThreeStage.rank_two_key`.) -/
lemma c_lt_half_b_fst (hlt : d.c 0 < d.c 1) : d.c 0 < d.b 0 / 2 := by
  have hp := p_eq d
  have hk := ckey d
  have hgap : 0 < d.c 1 - d.c 0 := by linarith
  have hid : 2 * (d.c 1 - d.c 0) * (d.c 0 - d.b 0 / 2)
      = -(12*(d.c 0)^2 - 6*d.c 0 + 1)/6 := by
    rw [eq_div_iff (by norm_num : (6:ℝ) ≠ 0)]
    linear_combination (-6)*hp - 12*hk
  have hnum : 0 < 12*(d.c 0)^2 - 6*d.c 0 + 1 := by nlinarith [sq_nonneg (6*d.c 0 - 1)]
  have hneg : 2 * (d.c 1 - d.c 0) * (d.c 0 - d.b 0 / 2) < 0 := by rw [hid]; linarith
  nlinarith [hneg, hgap]

/-- The mirror obstruction: if `c₂ < c₁` then `c₂ < q/2`. -/
lemma c_lt_half_b_snd (hlt : d.c 1 < d.c 0) : d.c 1 < d.b 1 / 2 := by
  have hq : d.b 1 * (d.c 0 - d.c 1) = d.c 0 - 1/2 := by
    have h1 := d.h1; have h2 := d.h2
    rw [sum2] at h1 h2
    linear_combination (d.c 0)*h1 - h2
  have hk : (d.c 0 - 1/2) * (1/2 - d.c 1) = 1/12 := by
    have hv := bvar d
    have hp' : d.b 0 * (d.c 0 - d.c 1) = 1/2 - d.c 1 := by
      have h1 := d.h1; have h2 := d.h2
      rw [sum2] at h1 h2
      linear_combination (-(d.c 1))*h1 + h2
    linear_combination hv - (1/2 - d.c 1)*hq - (d.b 1 * (d.c 0 - d.c 1))*hp'
  have hgap : 0 < d.c 0 - d.c 1 := by linarith
  have hid : 2 * (d.c 0 - d.c 1) * (d.c 1 - d.b 1 / 2)
      = -(12*(d.c 1)^2 - 6*d.c 1 + 1)/6 := by
    rw [eq_div_iff (by norm_num : (6:ℝ) ≠ 0)]
    linear_combination (-6)*hq - 12*hk
  have hnum : 0 < 12*(d.c 1)^2 - 6*d.c 1 + 1 := by nlinarith [sq_nonneg (6*d.c 1 - 1)]
  have hneg : 2 * (d.c 0 - d.c 1) * (d.c 1 - d.b 1 / 2) < 0 := by rw [hid]; linarith
  nlinarith [hneg, hgap]

/-- **The Claim is inconsistent at two stages.** -/
theorem two_stage_claim_inconsistent : ¬ Nonempty Data2 := by
  rintro ⟨d⟩
  rcases lt_trichotomy (d.c 0) (d.c 1) with hlt | heq | hgt
  · linarith [diag_lower_fst d, diag_upper_fst d, c_lt_half_b_fst d hlt]
  · exact cne d heq
  · linarith [diag_lower_snd d, diag_upper_snd d, c_lt_half_b_snd d hgt]

/-- Restated with the tableau supplied as explicit arguments. -/
theorem no_two_stage_tableau
    (A R : ℕ → ℕ → ℝ) (b c : ℕ → ℝ)
    (hA : ∀ i ∈ range 2, ∀ j ∈ range 2, 0 ≤ A i j)
    (hRsymm : ∀ i ∈ range 2, ∀ j ∈ range 2, R i j = R j i)
    (hRpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 2, ∑ j ∈ range 2, R i j * (x i * x j))
    (hb : ∀ i ∈ range 2, b i = ∑ j ∈ range 2, R i j)
    (hbnn : ∀ i ∈ range 2, 0 ≤ b i)
    (hc : ∀ i ∈ range 2, c i = ∑ j ∈ range 2, A i j)
    (hMpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 2, ∑ j ∈ range 2,
      ((∑ k ∈ range 2, R i k * A k j) + (∑ k ∈ range 2, R j k * A k i) - b i * b j)
        * (x i * x j))
    (h1 : ∑ i ∈ range 2, b i = 1)
    (h2 : ∑ i ∈ range 2, b i * c i = 1/2)
    (h3 : ∑ i ∈ range 2, b i * (c i)^2 = 1/3)
    (h4 : ∑ i ∈ range 2, b i * ∑ j ∈ range 2, A i j * c j = 1/6) :
    False :=
  two_stage_claim_inconsistent
    ⟨{ A := A, R := R, b := b, c := c, hA := hA, hRsymm := hRsymm, hRpsd := hRpsd,
       hb := hb, hbnn := hbnn, hc := hc, hMpsd := hMpsd,
       h1 := h1, h2 := h2, h3 := h3, h4 := h4 }⟩

end SSP.TwoStage
