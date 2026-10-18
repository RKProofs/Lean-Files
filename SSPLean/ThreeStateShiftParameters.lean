import SSPLean.ThreeStateCubicCoefficients

set_option autoImplicit false
open Set
namespace SSP.ThreeState

set_option maxHeartbeats 1000000 in
/-- At the upper endpoint of the admissible shift interval, the determinant
has a square lower bound. -/
theorem shift_endpoint_nonneg {d e F J r : ℝ}
    (hd : 0 ≤ d) (he : 0 ≤ e) (hde : d ≤ e) (hF : 0 ≤ F)
    (hJ : -e*F ≤ J) (hr : 0 ≤ r)
    (hr2 : r^2 = d^2-d*e+e^2+3*F) :
    0 ≤ J+(d*e-F)*((2*r-d-e)/3)+
      (d+e)*((2*r-d-e)/3)^2+((2*r-d-e)/3)^3 := by
  have hrbound : d ≤ 2*r := by
    nlinarith [sq_nonneg (e-d),sq_nonneg (2*r+d)]
  have hfac : 0 ≤ -d+2*e+2*r := by linarith
  have hprod := mul_nonneg hfac (sq_nonneg (d-2*e+r))
  have hid :
      27*(J+(d*e-F)*((2*r-d-e)/3)+
        (d+e)*((2*r-d-e)/3)^2+((2*r-d-e)/3)^3) =
      (-d+2*e+2*r)*(d-2*e+r)^2+27*(J+e*F)+
        (3*(-d+2*e+2*r))*(r^2-(d^2-d*e+e^2+3*F)) := by ring
  rw [hr2,sub_self,mul_zero,add_zero] at hid
  nlinarith

set_option maxHeartbeats 1000000 in
/-- The smaller/larger roots of a quadratic with nonnegative sum and product. -/
theorem nonneg_quadratic_roots {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hD : 0 ≤ T^2-4*K) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ a+b = T ∧ a*b = K := by
  let z := Real.sqrt (T^2-4*K)
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hz2 : z^2 = T^2-4*K := Real.sq_sqrt hD
  have hzT : z ≤ T := by nlinarith [sq_nonneg (z+T)]
  refine ⟨(T-z)/2,(T+z)/2,?_,?_,?_,?_⟩ <;> nlinarith

set_option maxHeartbeats 1000000 in
/-- Generic admissible shift, with the alternatives needed for entrywise positivity. -/
theorem exists_admissible_shift {T K J r : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ T^2-4*K) (hr : 0 ≤ r)
    (hr2 : r^2 = T^2-3*K)
    (hUQ : 0 ≤ J+K*((2*r-T)/3)+T*((2*r-T)/3)^2+((2*r-T)/3)^3) :
    ∃ t a b Q : ℝ, 0 ≤ t ∧ 0 ≤ a ∧ a ≤ b ∧ 0 ≤ Q ∧
      a+b = T+3*t ∧ a*b = K+2*T*t+3*t^2 ∧
      Q = J+K*t+T*t^2+t^3 ∧ (t = 0 ∨ a = 0 ∨ Q = 0) := by
  have hU : 0 ≤ (2*r-T)/3 := by nlinarith [sq_nonneg (2*r+T)]
  by_cases hK : 0 ≤ K
  · by_cases hJ : 0 ≤ J
    · obtain ⟨a,b,ha,hab,hs,hp⟩ := nonneg_quadratic_roots hT hK hD
      exact ⟨0,a,b,J,le_rfl,ha,hab,hJ,by simpa using hs,
        by simpa using hp,by ring,Or.inl rfl⟩
    · have hJneg : J < 0 := lt_of_not_ge hJ
      let U := (2*r-T)/3
      let q := fun t : ℝ => J+K*t+T*t^2+t^3
      obtain ⟨t,ht,heq⟩ := intermediate_value_Icc hU (by dsimp [q]; fun_prop)
        (show 0 ∈ Icc (q 0) (q U) by simpa [q,U] using And.intro hJneg.le hUQ)
      have ht0 : 0 ≤ t := ht.1
      have hKt : 0 ≤ K+2*T*t+3*t^2 := by positivity
      have hDt : 0 ≤ (T+3*t)^2-4*(K+2*T*t+3*t^2) := by
        have hbound : 0 ≤ (U-t)*(2*T+3*(U+t)) := mul_nonneg
          (sub_nonneg.mpr ht.2) (by dsimp [U]; nlinarith [ht0])
        dsimp [U] at *
        nlinarith
      obtain ⟨a,b,ha,hab,hs,hp⟩ := nonneg_quadratic_roots (by positivity) hKt hDt
      exact ⟨t,a,b,0,ht.1,ha,hab,le_rfl,hs,hp,heq.symm,Or.inr (Or.inr rfl)⟩
  · have hKneg : K < 0 := lt_of_not_ge hK
    have hrT : T < r := by nlinarith [sq_nonneg (r+T)]
    let L := (r-T)/3
    let U := (2*r-T)/3
    let q := fun t : ℝ => J+K*t+T*t^2+t^3
    have hL : 0 ≤ L := by dsimp [L]; linarith
    have hLU : L ≤ U := by dsimp [L,U]; linarith
    have hKL : K+2*T*L+3*L^2 = 0 := by dsimp [L]; nlinarith
    by_cases hqL : 0 ≤ q L
    · refine ⟨L,0,T+3*L,q L,hL,le_rfl,by positivity,hqL,by ring,?_,rfl,Or.inr (Or.inl rfl)⟩
      simpa using hKL.symm
    · obtain ⟨t,ht,heq⟩ := intermediate_value_Icc hLU (by dsimp [q]; fun_prop)
        (show 0 ∈ Icc (q L) (q U) from ⟨(lt_of_not_ge hqL).le,hUQ⟩)
      have ht0 : 0 ≤ t := hL.trans ht.1
      have hKt : 0 ≤ K+2*T*t+3*t^2 := by
        have hbound := mul_nonneg (sub_nonneg.mpr ht.1)
          (show 0 ≤ 2*T+3*(t+L) by positivity)
        nlinarith
      have hDt : 0 ≤ (T+3*t)^2-4*(K+2*T*t+3*t^2) := by
        have hbound := mul_nonneg (sub_nonneg.mpr ht.2)
          (show 0 ≤ 2*T+3*(U+t) by dsimp [U]; nlinarith)
        dsimp [U] at *
        nlinarith
      obtain ⟨a,b,ha,hab,hs,hp⟩ := nonneg_quadratic_roots (by positivity) hKt hDt
      exact ⟨t,a,b,0,ht0,ha,hab,le_rfl,hs,hp,heq.symm,Or.inr (Or.inr rfl)⟩

set_option maxHeartbeats 1000000 in
theorem endpoint_of_diagonal_data {T K J d e r : ℝ}
    (hd : 0 ≤ d) (he : 0 ≤ e) (hde : d ≤ e)
    (hT : T = d+e) (hK : K ≤ d*e) (hJ : -e*(d*e-K) ≤ J)
    (hr : 0 ≤ r) (hr2 : r^2 = T^2-3*K) :
    0 ≤ J+K*((2*r-T)/3)+T*((2*r-T)/3)^2+((2*r-T)/3)^3 := by
  have h := shift_endpoint_nonneg hd he hde (sub_nonneg.mpr hK) hJ hr
    (show r^2 = d^2-d*e+e^2+3*(d*e-K) by rw [hT] at hr2; nlinarith)
  simpa [hT,sub_add_eq_sub_sub] using h

set_option maxHeartbeats 1000000 in
theorem zeroDiagonal_endpoint_nonneg (N : Mat) (hN : ∀ i j, 0 ≤ N i j)
    (hz : N 0 0 = 0 ∨ N 1 1 = 0 ∨ N 2 2 = 0) {r : ℝ}
    (hr : 0 ≤ r) (hr2 : r^2 = (traceCoeff N)^2-3*pairCoeff N) :
    0 ≤ detCoeff N+pairCoeff N*((2*r-traceCoeff N)/3)+
      traceCoeff N*((2*r-traceCoeff N)/3)^2+((2*r-traceCoeff N)/3)^3 := by
  have hp := pairCoeff_le_diagonal_products N hN
  have p01 := mul_nonneg (hN 0 1) (hN 1 0)
  have p02 := mul_nonneg (hN 0 2) (hN 2 0)
  have p12 := mul_nonneg (hN 1 2) (hN 2 1)
  have c1 := mul_nonneg (mul_nonneg (hN 0 1) (hN 1 2)) (hN 2 0)
  have c2 := mul_nonneg (mul_nonneg (hN 0 2) (hN 1 0)) (hN 2 1)
  rcases hz with hz | hz | hz
  · by_cases horder : N 1 1 ≤ N 2 2
    · apply endpoint_of_diagonal_data (d := N 1 1) (e := N 2 2)
        (hN 1 1) (hN 2 2) horder
      · simp [traceCoeff,hz]
      · dsimp [pairCoeff] at hp ⊢; rw [hz] at hp ⊢; nlinarith
      · have m1 := mul_nonneg (hN 2 2) p01
        have m2 := mul_nonneg (hN 2 2) p02
        have m3 := mul_nonneg (hN 2 2) p12
        have g1 := mul_nonneg (show 0 ≤ N 2 2-N 1 1 by linarith) p01
        have g2 := mul_nonneg (show 0 ≤ N 2 2-N 1 1 by linarith) p02
        have g3 := mul_nonneg (show 0 ≤ N 2 2-N 1 1 by linarith) p12
        dsimp [detCoeff,pairCoeff]
        rw [hz]
        nlinarith
      · exact hr
      · exact hr2
    · apply endpoint_of_diagonal_data (d := N 2 2) (e := N 1 1)
        (hN 2 2) (hN 1 1) (le_of_not_ge horder)
      · simp [traceCoeff,hz]; ring
      · dsimp [pairCoeff] at hp ⊢; rw [hz] at hp ⊢; nlinarith
      · have m1 := mul_nonneg (hN 1 1) p01
        have m2 := mul_nonneg (hN 1 1) p02
        have m3 := mul_nonneg (hN 1 1) p12
        have g1 := mul_nonneg (show 0 ≤ N 1 1-N 2 2 by linarith) p01
        have g2 := mul_nonneg (show 0 ≤ N 1 1-N 2 2 by linarith) p02
        have g3 := mul_nonneg (show 0 ≤ N 1 1-N 2 2 by linarith) p12
        dsimp [detCoeff,pairCoeff]
        rw [hz]
        nlinarith
      · exact hr
      · exact hr2
  · by_cases horder : N 0 0 ≤ N 2 2
    · apply endpoint_of_diagonal_data (d := N 0 0) (e := N 2 2)
        (hN 0 0) (hN 2 2) horder
      · simp [traceCoeff,hz]
      · dsimp [pairCoeff] at hp ⊢; rw [hz] at hp ⊢; nlinarith
      · have m1 := mul_nonneg (hN 2 2) p01
        have m2 := mul_nonneg (hN 2 2) p02
        have m3 := mul_nonneg (hN 2 2) p12
        have g1 := mul_nonneg (show 0 ≤ N 2 2-N 0 0 by linarith) p01
        have g2 := mul_nonneg (show 0 ≤ N 2 2-N 0 0 by linarith) p02
        have g3 := mul_nonneg (show 0 ≤ N 2 2-N 0 0 by linarith) p12
        dsimp [detCoeff,pairCoeff]
        rw [hz]
        nlinarith
      · exact hr
      · exact hr2
    · apply endpoint_of_diagonal_data (d := N 2 2) (e := N 0 0)
        (hN 2 2) (hN 0 0) (le_of_not_ge horder)
      · simp [traceCoeff,hz]; ring
      · dsimp [pairCoeff] at hp ⊢; rw [hz] at hp ⊢; nlinarith
      · have m1 := mul_nonneg (hN 0 0) p01
        have m2 := mul_nonneg (hN 0 0) p02
        have m3 := mul_nonneg (hN 0 0) p12
        have g1 := mul_nonneg (show 0 ≤ N 0 0-N 2 2 by linarith) p01
        have g2 := mul_nonneg (show 0 ≤ N 0 0-N 2 2 by linarith) p02
        have g3 := mul_nonneg (show 0 ≤ N 0 0-N 2 2 by linarith) p12
        dsimp [detCoeff,pairCoeff]
        rw [hz]
        nlinarith
      · exact hr
      · exact hr2
  · by_cases horder : N 0 0 ≤ N 1 1
    · apply endpoint_of_diagonal_data (d := N 0 0) (e := N 1 1)
        (hN 0 0) (hN 1 1) horder
      · simp [traceCoeff,hz]
      · dsimp [pairCoeff] at hp ⊢; rw [hz] at hp ⊢; nlinarith
      · have m1 := mul_nonneg (hN 1 1) p01
        have m2 := mul_nonneg (hN 1 1) p02
        have m3 := mul_nonneg (hN 1 1) p12
        have g1 := mul_nonneg (show 0 ≤ N 1 1-N 0 0 by linarith) p01
        have g2 := mul_nonneg (show 0 ≤ N 1 1-N 0 0 by linarith) p02
        have g3 := mul_nonneg (show 0 ≤ N 1 1-N 0 0 by linarith) p12
        dsimp [detCoeff,pairCoeff]
        rw [hz]
        nlinarith
      · exact hr
      · exact hr2
    · apply endpoint_of_diagonal_data (d := N 1 1) (e := N 0 0)
        (hN 1 1) (hN 0 0) (le_of_not_ge horder)
      · simp [traceCoeff,hz]; ring
      · dsimp [pairCoeff] at hp ⊢; rw [hz] at hp ⊢; nlinarith
      · have m1 := mul_nonneg (hN 0 0) p01
        have m2 := mul_nonneg (hN 0 0) p02
        have m3 := mul_nonneg (hN 0 0) p12
        have g1 := mul_nonneg (show 0 ≤ N 0 0-N 1 1 by linarith) p01
        have g2 := mul_nonneg (show 0 ≤ N 0 0-N 1 1 by linarith) p02
        have g3 := mul_nonneg (show 0 ≤ N 0 0-N 1 1 by linarith) p12
        dsimp [detCoeff,pairCoeff]
        rw [hz]
        nlinarith
      · exact hr
      · exact hr2

set_option maxHeartbeats 1000000 in
/-- Every nonnegative matrix with a zero diagonal admits the canonical cubic
and an entrywise nonnegative initial projection after a nonnegative shift. -/
theorem zeroDiagonal_canonical_parameters (N : Mat) (hN : ∀ i j, 0 ≤ N i j)
    (hz : N 0 0 = 0 ∨ N 1 1 = 0 ∨ N 2 2 = 0) :
    ∃ t a b Q : ℝ, 0 ≤ t ∧ 0 ≤ a ∧ a ≤ b ∧ 0 ≤ Q ∧
      (N+t • (1 : Mat))^3 =
        (a+b) • (N+t • (1 : Mat))^2-(a*b) • (N+t • (1 : Mat))+Q • (1 : Mat) ∧
      (∀ i j, 0 ≤ (N+t • (1 : Mat)) i j) ∧
      (∀ i j, 0 ≤ ((N+t • (1 : Mat))^2-a • (N+t • (1 : Mat))) i j) := by
  have hT : 0 ≤ traceCoeff N := by dsimp [traceCoeff]; linarith [hN 0 0,hN 1 1,hN 2 2]
  have hD := zeroDiagonal_discriminant_nonneg N hN hz
  have hDelta : 0 ≤ (traceCoeff N)^2-3*pairCoeff N := by
    nlinarith [sq_nonneg (traceCoeff N)]
  let r := Real.sqrt ((traceCoeff N)^2-3*pairCoeff N)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = (traceCoeff N)^2-3*pairCoeff N := Real.sq_sqrt hDelta
  obtain ⟨t,a,b,Q,ht,ha,hab,hQ,hs,hp,hq,halt⟩ := exists_admissible_shift hT hD hr hr2
    (zeroDiagonal_endpoint_nonneg N hN hz hr hr2)
  let M := N+t • (1 : Mat)
  have hM : ∀ i j, 0 ≤ M i j := by
    intro i j
    change 0 ≤ (N+t • (1 : Mat)) i j
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    exact add_nonneg (hN i j) (mul_nonneg ht (by simp [Matrix.one_apply]; split <;> norm_num))
  have hcubic : M^3 = (a+b) • M^2-(a*b) • M+Q • (1 : Mat) := by
    dsimp [M]
    rw [hs,hp,hq]
    exact shifted_matrix_cubic N t
  refine ⟨t,a,b,Q,ht,ha,hab,hQ,hcubic,hM,?_⟩
  rcases halt with ht0 | ha0 | hQ0
  · subst t
    simpa [M] using zeroDiagonal_projection_nonneg N hN hz ha hab
      (by simpa using hs) (by simpa using hp)
  · subst a
    simpa using SSP.Survival.pow_nonneg_entry M hM 2
  · have hc : M^3 = (a+b) • M^2-(a*b) • M := by simpa [hQ0] using hcubic
    exact realRoot_projection_nonneg M hM ha hab hc

end SSP.ThreeState
