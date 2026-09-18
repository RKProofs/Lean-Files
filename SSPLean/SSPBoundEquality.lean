import SSPLean.MainRevised
import SSPLean.QSequenceEquality

/-!
# Equality in the second-order SSP bound

This module reverses the weighted Cauchy--Schwarz endgame used to prove
`r ≤ 2s`.  It first characterizes equality for the abstract
`ComponentBound` formulation, and then identifies every positively weighted
component of a genuine substochastic resolvent as a serial equal-rate chain.
-/

open Finset Matrix

set_option autoImplicit false

namespace SSP

/-- A serial Erlang chain with the rate forced by the endpoint `r = 2s`.
The transient states may be relabeled, but the distinguished state `i` is
the first phase. -/
def IsHalfRateSerialErlang {s : ℕ} (hs : 0 < s)
    (Q : Matrix (Fin s) (Fin s) ℝ) (i : Fin s) : Prop :=
  ∃ v : Fin s ≃ Fin s,
    v ⟨0, hs⟩ = i ∧
      ∀ r c : Fin s,
        Q (v r) (v c) =
          if c = r then 1 / 2
          else if c.val = r.val + 1 then 1 / 2 else 0

private theorem halfRateSerial_matrix_eq
    {s : ℕ} {hs : 0 < s} {Q : Matrix (Fin s) (Fin s) ℝ} {i : Fin s}
    (h : IsHalfRateSerialErlang hs Q i) :
    ∃ v : Fin s ≃ Fin s, v ⟨0, hs⟩ = i ∧
      Q = (Matrix.reindex v v)
        (QSequenceEquality.serialErlangQ s (1 / 2)) := by
  obtain ⟨v, hv0, hQ⟩ := h
  refine ⟨v, hv0, ?_⟩
  ext a b
  have hab := hQ (v.symm a) (v.symm b)
  change Q a b =
    QSequenceEquality.serialErlangQ s (1 / 2) (v.symm a) (v.symm b)
  rw [QSequenceEquality.serialErlangQ_apply,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  simpa only [Equiv.apply_symm_apply] using hab

theorem IsHalfRateSerialErlang.qsequence_moments
    {s : ℕ} {hs : 0 < s} {Q : ℕ → ℕ → ℝ} {i : ℕ} (hi : i < s)
    (hRho : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (h : IsHalfRateSerialErlang hs (toMat s Q) ⟨i, hi⟩) :
    xVec s Q i = 2 * s ∧ yVec s Q i = 2 * s * (s + 1) := by
  obtain ⟨v, hv0, hQeq⟩ := halfRateSerial_matrix_eq h
  have hden : (1 : Matrix (Fin s) (Fin s) ℝ) - toMat s Q =
      (Matrix.reindex v v)
        (1 - QSequenceEquality.serialErlangQ s (1 / 2)) := by
    rw [hQeq]
    ext a b
    simp [Matrix.reindex_apply, Matrix.one_apply]
  have hmom := QSequenceEquality.reindex_resolvent_moments v
    (1 - QSequenceEquality.serialErlangQ s (1 / 2)) ⟨0, hs⟩
  constructor
  · rw [QSequenceEquality.xVec_eq_resolvent_apply s Q hRho i hi,
      hden, ← hv0, hmom.1,
      QSequenceEquality.serialErlangQ_fundamental (by norm_num) ⟨0, hs⟩]
    norm_num
  · rw [QSequenceEquality.yVec_eq_resolvent_second_apply s Q hRho i hi,
      hden, ← hv0, hmom.2,
      QSequenceEquality.serialErlangQ_second (by norm_num) ⟨0, hs⟩]
    simp [K2Concrete.erlangV2, K2Concrete.erlangV1]
    ring

theorem halfRateSerialErlang_of_serial_of_firstMoment
    {s : ℕ} {hs : 0 < s} {Q : ℕ → ℕ → ℝ} {i : ℕ} (hi : i < s)
    (hRho : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (hserial : QSequenceEquality.IsSerialErlang hs (toMat s Q) ⟨i, hi⟩)
    (hx : xVec s Q i = 2 * s) :
    IsHalfRateSerialErlang hs (toMat s Q) ⟨i, hi⟩ := by
  obtain ⟨lam, hlam0, _hlam1, v, hv0, hQ⟩ := hserial
  have hQeq : toMat s Q = (Matrix.reindex v v)
      (QSequenceEquality.serialErlangQ s lam) := by
    ext a b
    have hab := hQ (v.symm a) (v.symm b)
    change toMat s Q a b =
      QSequenceEquality.serialErlangQ s lam (v.symm a) (v.symm b)
    rw [QSequenceEquality.serialErlangQ_apply]
    simpa only [Equiv.apply_symm_apply] using hab
  have hden : (1 : Matrix (Fin s) (Fin s) ℝ) - toMat s Q =
      (Matrix.reindex v v)
        (1 - QSequenceEquality.serialErlangQ s lam) := by
    rw [hQeq]
    ext a b
    simp [Matrix.reindex_apply, Matrix.one_apply]
  have hx' : ((1 - toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ))) ⟨i, hi⟩ =
      2 * s := by
    rw [← QSequenceEquality.xVec_eq_resolvent_apply s Q hRho i hi]
    exact hx
  have hfirst := (QSequenceEquality.reindex_resolvent_moments v
    (1 - QSequenceEquality.serialErlangQ s lam) ⟨0, hs⟩).1
  rw [hden, ← hv0, hfirst,
    QSequenceEquality.serialErlangQ_fundamental hlam0.ne' ⟨0, hs⟩] at hx'
  norm_num at hx'
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hinv : lam⁻¹ = 2 := by
    rcases hx' with hinv | hs0
    · exact hinv
    · omega
  have hlamHalf : lam = 1 / 2 := by
    have hcancel : lam⁻¹ * lam = 1 := inv_mul_cancel₀ hlam0.ne'
    nlinarith
  refine ⟨v, hv0, ?_⟩
  intro r c
  rw [hlamHalf] at hQ
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hQ
  exact hQ r c

/-- The exact equality data left by the abstract proof of `r ≤ 2s`.
Only indices in `range s` are relevant, matching `rowSum` and `rowSum2`. -/
def AttainsSSPBound (s : ℕ) (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ) : Prop :=
  ∑ i ∈ range s, w i = 1 ∧
    ∀ i < s, 0 < w i →
      rowSum s N i = 2 * s ∧
      rowSum2 s N i = 2 * s * (s + 1)

/-- Equality in the abstract SSP endgame occurs exactly when the weights form
a probability vector supported on components having the two extremal
resolvent moments. -/
theorem orderTwo_two_mul_iff_attainsSSPBound
    (s : ℕ) (hs : 0 < s) (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (hCB : ComponentBound s N) :
    MainRevised.OrderTwo s N w (2 * s) ↔ AttainsSSPBound s N w := by
  let u := rowSum s N
  let v := rowSum2 s N
  let K : ℝ := 2 * s / (s + 1)
  let W : ℝ := ∑ i ∈ range s, w i
  let U2 : ℝ := ∑ i ∈ range s, w i * (u i)^2
  constructor
  · rintro ⟨hoc1, hoc2⟩
    have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
    have hK : 0 < K := by dsimp [K]; positivity
    have hW0 : 0 ≤ W := by
      dsimp [W]
      exact sum_nonneg fun i _ => hw i
    have hU20 : 0 ≤ U2 := by
      dsimp [U2]
      exact sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
    have hV : ∑ i ∈ range s, w i * v i = 2 * s * (s + 1) := by
      dsimp [v]
      rw [hoc2]
      ring
    have hU : ∑ i ∈ range s, w i * u i = 2 * s := by
      simpa [u] using hoc1
    have hU2le : U2 ≤ K * ∑ i ∈ range s, w i * v i := by
      dsimp [U2]
      rw [mul_sum]
      apply sum_le_sum
      intro i hi
      simpa [u, v, K, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left (hCB i (mem_range.1 hi)) (hw i)
    have hKV : K * ∑ i ∈ range s, w i * v i = (2 * s)^2 := by
      rw [hV]
      dsimp [K]
      field_simp
    have hcs : (∑ i ∈ range s, w i * u i)^2 ≤ W * U2 := by
      have h := sum_mul_sq_le_sq_mul_sq (range s)
        (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * u i)
      have e1 : ∀ i ∈ range s,
          Real.sqrt (w i) * (Real.sqrt (w i) * u i) = w i * u i := by
        intro i _
        rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
      have e2 : ∀ i ∈ range s, Real.sqrt (w i)^2 = w i :=
        fun i _ => Real.sq_sqrt (hw i)
      have e3 : ∀ i ∈ range s,
          (Real.sqrt (w i) * u i)^2 = w i * (u i)^2 := by
        intro i _
        rw [mul_pow, Real.sq_sqrt (hw i)]
      simpa only [sum_congr rfl e1, sum_congr rfl e2,
        sum_congr rfl e3, W, U2] using h
    have hU2upper : U2 ≤ (2 * s)^2 := by linarith [hU2le, hKV]
    have hWU2 : W * U2 ≤ U2 := by
      exact mul_le_of_le_one_left hU20 (show W ≤ 1 by simpa [W] using hw1)
    have hU2eq : U2 = (2 * s)^2 := by
      rw [hU] at hcs
      linarith
    have hWeq : W = 1 := by
      rw [hU, hU2eq] at hcs
      have hpos : 0 < (2 * (s : ℝ))^2 := sq_pos_of_pos (by positivity)
      nlinarith
    refine ⟨by simpa [W] using hWeq, ?_⟩
    intro i hi hwi
    have hiMem : i ∈ range s := mem_range.2 hi
    have hvariance :
        ∑ j ∈ range s, w j * (u j - 2 * s)^2 = 0 := by
      have hid :
          ∑ j ∈ range s, w j * (u j - 2 * s)^2 =
            U2 - 2 * (2 * s) * (∑ j ∈ range s, w j * u j)
              + (2 * s)^2 * W := by
        dsimp [U2, W]
        calc
          ∑ j ∈ range s, w j * (u j - 2 * s)^2 =
              ∑ j ∈ range s,
                (w j * (u j)^2 - 2 * (2 * s) * (w j * u j)
                  + (2 * s)^2 * w j) := by
                    apply sum_congr rfl
                    intro j _
                    ring
          _ = _ := by
            rw [sum_add_distrib, sum_sub_distrib]
            simp_rw [← mul_sum]
      rw [hid, hU, hU2eq, hWeq]
      ring
    have htermVar : w i * (u i - 2 * s)^2 ≤ 0 := by
      rw [← hvariance]
      exact single_le_sum
        (fun j _ => mul_nonneg (hw j) (sq_nonneg (u j - 2 * s))) hiMem
    have hui : u i = 2 * s := by
      have : (u i - 2 * s)^2 = 0 := by nlinarith
      nlinarith [sq_nonneg (u i - 2 * s)]
    have hslack :
        ∑ j ∈ range s, w j * (K * v j - (u j)^2) = 0 := by
      calc
        ∑ j ∈ range s, w j * (K * v j - (u j)^2) =
            ∑ j ∈ range s, (K * (w j * v j) - w j * (u j)^2) := by
              apply sum_congr rfl
              intro j _
              ring
        _ = K * (∑ j ∈ range s, w j * v j) - U2 := by
              dsimp [U2]
              rw [sum_sub_distrib, mul_sum]
        _ = 0 := by rw [hKV, hU2eq]; ring
    have htermSlack : w i * (K * v i - (u i)^2) ≤ 0 := by
      rw [← hslack]
      apply single_le_sum _ hiMem
      intro j hj
      exact mul_nonneg (hw j)
        (sub_nonneg.mpr (hCB j (mem_range.1 hj)))
    have hcomponent : (u i)^2 = K * v i := by
      have hnonneg : 0 ≤ K * v i - (u i)^2 :=
        sub_nonneg.mpr (hCB i hi)
      nlinarith
    have hui' : rowSum s N i = 2 * s := by simpa [u] using hui
    refine ⟨hui', ?_⟩
    dsimp [K, u, v] at hcomponent ⊢
    rw [hui'] at hcomponent
    field_simp at hcomponent
    nlinarith
  · intro hattain
    rcases hattain with ⟨hW, hsupp⟩
    constructor
    · calc
        ∑ i ∈ range s, w i * rowSum s N i =
            ∑ i ∈ range s, w i * (2 * s) := by
              apply sum_congr rfl
              intro i hi
              by_cases hwi0 : w i = 0
              · simp [hwi0]
              · rw [(hsupp i (mem_range.1 hi) (lt_of_le_of_ne (hw i) (Ne.symm hwi0))).1]
        _ = 2 * s := by rw [← sum_mul, hW, one_mul]
    · calc
        ∑ i ∈ range s, w i * rowSum2 s N i =
            ∑ i ∈ range s, w i * (2 * s * (s + 1)) := by
              apply sum_congr rfl
              intro i hi
              by_cases hwi0 : w i = 0
              · simp [hwi0]
              · rw [(hsupp i (mem_range.1 hi) (lt_of_le_of_ne (hw i) (Ne.symm hwi0))).2]
        _ = 2 * s + (2 * s)^2 / 2 := by
              rw [← sum_mul, hW]
              ring

/-- In the genuine substochastic-resolvent setting, every component carrying
positive final weight is a serial equal-rate Erlang chain starting at that
component. -/
theorem orderTwo_two_mul_implies_supported_serialErlang
    (s : ℕ) (hs : 0 < s) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (hRho : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (hoc : MainRevised.OrderTwo s (Nmat s Q) w (2 * s)) :
    ∑ i ∈ range s, w i = 1 ∧
      ∀ i (hi : i < s), 0 < w i →
        QSequenceEquality.IsSerialErlang hs (toMat s Q) ⟨i, hi⟩ ∧
        xVec s Q i = 2 * s := by
  have hattain := (orderTwo_two_mul_iff_attainsSSPBound s hs (Nmat s Q) w
    hw hw1 (componentBound_unconditional s Q hQ hsub hRho hs)).mp hoc
  rcases hattain with ⟨hW, hsupp⟩
  refine ⟨hW, ?_⟩
  intro i hi hwi
  obtain ⟨hu, hv⟩ := hsupp i hi hwi
  have hx : xVec s Q i = 2 * s := by
    rwa [← rowSum_eq_xVec]
  have heq : (xVec s Q i)^2 =
      (2 * (s : ℝ) / ((s : ℝ) + 1)) * yVec s Q i := by
    rw [← rowSum_eq_xVec, ← rowSum2_eq_yVec, hu, hv]
    field_simp
  exact ⟨(QSequenceEquality.component_eq_iff_isSerialErlang
    s Q hQ hsub hRho hs i hi).mp heq, hx⟩

/-- Complete equality data for the genuine q-sequence problem: the weights
form a probability vector and every positively weighted starting state is
the first phase of the half-rate serial Erlang chain. -/
def AttainsQSequenceSSPBound
    (s : ℕ) (hs : 0 < s) (Q : ℕ → ℕ → ℝ) (w : ℕ → ℝ) : Prop :=
  ∑ i ∈ range s, w i = 1 ∧
    ∀ i (hi : i < s), 0 < w i →
      IsHalfRateSerialErlang hs (toMat s Q) ⟨i, hi⟩

/-- **General equality theorem for `r ≤ 2s`.**

For a nonnegative substochastic q-sequence with spectral radius below one,
the second-order conditions hold at the extremal value `r = 2s` if and only
if all final weight is carried by first phases of serial Erlang chains with
common transition/absorption parameter `1/2`. -/
theorem orderTwo_two_mul_iff_halfRateSerialErlang
    (s : ℕ) (hs : 0 < s) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (hRho : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i ∈ range s, w i ≤ 1) :
    MainRevised.OrderTwo s (Nmat s Q) w (2 * s) ↔
      AttainsQSequenceSSPBound s hs Q w := by
  constructor
  · intro hoc
    obtain ⟨hW, hsupp⟩ := orderTwo_two_mul_implies_supported_serialErlang
      s hs Q hQ hsub hRho w hw hw1 hoc
    refine ⟨hW, ?_⟩
    intro i hi hwi
    obtain ⟨hserial, hx⟩ := hsupp i hi hwi
    exact halfRateSerialErlang_of_serial_of_firstMoment hi hRho hserial hx
  · rintro ⟨hW, hsupp⟩
    apply (orderTwo_two_mul_iff_attainsSSPBound s hs (Nmat s Q) w hw hw1
      (componentBound_unconditional s Q hQ hsub hRho hs)).mpr
    refine ⟨hW, ?_⟩
    intro i hi hwi
    have hmom := (hsupp i hi hwi).qsequence_moments hi hRho
    constructor
    · rw [rowSum_eq_xVec]
      exact hmom.1
    · rw [rowSum2_eq_yVec]
      exact hmom.2

end SSP
