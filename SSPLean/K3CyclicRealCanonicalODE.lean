import SSPLean.K3CyclicRealCanonicalBridge
import SSPLean.CubicODEUniqueness

/-!
# Third derivative of the canonical real-root first-start series

The curvature certificate needs only two derivatives.  Identification with
the canonical scalar ODE also needs the third derivative.  This file supplies
that analytic step without changing any certificate module.
-/

set_option autoImplicit false

namespace SSP.K3CyclicRealTail

/-- The third derivative series of the normalized first-start remainder. -/
noncomputable def firstStartRemainderDeriv3 (u v t : ℝ) : ℝ :=
  ∑' n, completeTaylorTerm u v 0 n t

/-- Absolute convergence at factorial shift zero. -/
theorem completeTaylorTerm_zero_summable
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Summable (fun n => completeTaylorTerm u v 0 n t) := by
  let R : ℝ := max 1 |t|
  let x : ℝ := 4 * R
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have huv0 : 0 ≤ u * v := mul_nonneg hu0 hv0
  have huv1 : u * v ≤ 1 := mul_le_one₀ hu1 hv0 hv1
  have hmajorant : Summable (fun n : ℕ =>
      4 * (x ^ n / (Nat.factorial n : ℝ))) :=
    (Real.summable_pow_div_factorial x).mul_left 4
  apply hmajorant.of_norm_bounded
  intro n
  have hnBase : (n + 1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self : n + 1 < 2 ^ (n + 1)).le
  have hnSq : (n + 1 : ℝ) ^ 2 ≤ 4 * (4 : ℝ) ^ n := by
    calc
      (n + 1 : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (n + 1)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hnBase 2
      _ = (4 : ℝ) ^ (n + 1) := by
        rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        congr 1
        omega
      _ = 4 * (4 : ℝ) ^ n := by rw [pow_succ']
  have htPow : |t| ^ n ≤ R ^ n :=
    pow_le_pow_left₀ (abs_nonneg t) (le_max_right _ _) _
  have hcomp0 : 0 ≤ complete3 u v n := complete3_nonneg hu0 hv0 n
  have hcomp : complete3 u v n ≤ (n + 1 : ℝ) ^ 2 :=
    complete3_le_sq hu0 hu1 hv0 hv1 n
  unfold completeTaylorTerm
  simp only [Nat.add_zero, norm_div, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg hu0, abs_of_nonneg hv0, abs_of_nonneg hcomp0, norm_pow]
  rw [abs_of_nonneg (by positivity : 0 ≤ (Nat.factorial n : ℝ))]
  rw [show 4 * (x ^ n / (Nat.factorial n : ℝ)) =
      (4 * x ^ n) / (Nat.factorial n : ℝ) by ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    u * v * complete3 u v n * |t| ^ n ≤
        1 * (n + 1 : ℝ) ^ 2 * |t| ^ n := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul huv1 hcomp hcomp0 (by norm_num))
        (pow_nonneg (abs_nonneg t) _)
    _ ≤ 1 * (4 * (4 : ℝ) ^ n) * |t| ^ n := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnSq (by norm_num))
        (pow_nonneg (abs_nonneg t) _)
    _ ≤ 1 * (4 * (4 : ℝ) ^ n) * R ^ n := by
      exact mul_le_mul_of_nonneg_left htPow (by positivity)
    _ = 4 * (4 : ℝ) ^ n * R ^ n := by ring
    _ = 4 * x ^ n := by simp [x, mul_pow]; ring

theorem firstStartRemainderDeriv2_hasDerivAt
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    HasDerivAt (firstStartRemainderDeriv2 u v)
      (firstStartRemainderDeriv3 u v t) t := by
  let B : ℝ := |t| + 1
  let majorant : ℕ → ℝ := fun n =>
    ‖completeTaylorTerm u v 0 n B‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmajorant : Summable majorant := by
    exact (completeTaylorTerm_zero_summable hu0 hu1 hv0 hv1 (t := B)).norm
  have htmem : t ∈ Set.Ioo (t - 1) (t + 1) := by constructor <;> linarith
  unfold firstStartRemainderDeriv2 firstStartRemainderDeriv3
  apply hasDerivAt_tsum_of_isPreconnected hmajorant
    (show IsOpen (Set.Ioo (t - 1) (t + 1)) from isOpen_Ioo)
    (show IsPreconnected (Set.Ioo (t - 1) (t + 1)) from
      Set.ordConnected_Ioo.isPreconnected)
  · intro n y hy
    exact completeTaylorTerm_hasDerivAt u v y 0 n
  · intro n y hy
    exact completeTaylorTerm_norm_mono hB
      (by
        have hdiff : |y - t| < 1 := by
          rw [abs_lt]
          constructor <;> linarith [hy.1, hy.2]
        calc
          |y| = |t + (y - t)| := by rw [show t + (y - t) = y by ring]
          _ ≤ |t| + |y - t| := abs_add_le _ _
          _ ≤ |t| + 1 := by linarith) 0 n
  · exact htmem
  · exact completeTaylorTerm_summable hu0 hu1 hv0 hv1 (k := 1) (by omega)
  · exact htmem

theorem firstStartRemainderDeriv2_deriv_eq
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    deriv (firstStartRemainderDeriv2 u v) t =
      firstStartRemainderDeriv3 u v t :=
  (firstStartRemainderDeriv2_hasDerivAt hu0 hu1 hv0 hv1).deriv

/-- The two-variable complete homogeneous polynomial has its usual
second-order characteristic recurrence. -/
theorem diagonal_rec (u v : ℝ) (n : ℕ) :
    diagonal u v (n + 2) =
      (u + v) * diagonal u v (n + 1) - u * v * diagonal u v n := by
  rw [show n + 2 = (n + 1) + 1 by omega, diagonal_succ,
    diagonal_succ, pow_succ]
  ring

/-- Characteristic recurrence for `h_n(1,u,v)`. -/
theorem complete3_rec (u v : ℝ) (n : ℕ) :
    complete3 u v (n + 3) =
      (1 + u + v) * complete3 u v (n + 2) -
        (u + v + u * v) * complete3 u v (n + 1) +
          u * v * complete3 u v n := by
  rw [show n + 3 = (n + 2) + 1 by omega, complete3_succ,
    show n + 2 = (n + 1) + 1 by omega, complete3_succ,
    show n + 1 = n + 1 by rfl, complete3_succ,
    diagonal_rec u v (n + 1), diagonal_rec u v n]
  ring

/-- The normalized Taylor function satisfies the monic cubic ODE whose
characteristic roots are `1`, `u`, and `v`. -/
theorem firstStartRemainder_cubic_ode
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    firstStartRemainderDeriv3 u v t =
      (1 + u + v) * firstStartRemainderDeriv2 u v t -
        (u + v + u * v) * firstStartRemainderDeriv u v t +
          u * v * (1 + firstStartRemainder u v t) := by
  let f0 : ℕ → ℝ := fun n => completeTaylorTerm u v 0 n t
  let f1 : ℕ → ℝ := fun n => completeTaylorTerm u v 1 n t
  let f2 : ℕ → ℝ := fun n => completeTaylorTerm u v 2 n t
  let f3 : ℕ → ℝ := fun n => completeTaylorTerm u v 3 n t
  have h0 : Summable f0 := completeTaylorTerm_zero_summable hu0 hu1 hv0 hv1
  have h1 : Summable f1 :=
    completeTaylorTerm_summable hu0 hu1 hv0 hv1 (k := 1) (by omega)
  have h2 : Summable f2 :=
    completeTaylorTerm_summable hu0 hu1 hv0 hv1 (k := 2) (by omega)
  have h3 : Summable f3 :=
    completeTaylorTerm_summable hu0 hu1 hv0 hv1 (k := 3) (by omega)
  have hpoint : ∀ n,
      f0 (n + 3) =
        (1 + u + v) * f1 (n + 2) -
          (u + v + u * v) * f2 (n + 1) + u * v * f3 n := by
    intro n
    dsimp [f0, f1, f2, f3]
    unfold completeTaylorTerm
    rw [complete3_rec]
    norm_num
    ring
  have h1shift : Summable (fun n => f1 (n + 2)) :=
    (summable_nat_add_iff 2).2 h1
  have h2shift : Summable (fun n => f2 (n + 1)) :=
    (summable_nat_add_iff 1).2 h2
  have h0split := h0.sum_add_tsum_nat_add 3
  have h1split := h1.sum_add_tsum_nat_add 2
  have h2split := h2.sum_add_tsum_nat_add 1
  have htail :
      (∑' n, f0 (n + 3)) =
        (1 + u + v) * (∑' n, f1 (n + 2)) -
          (u + v + u * v) * (∑' n, f2 (n + 1)) +
            u * v * (∑' n, f3 n) := by
    rw [tsum_congr hpoint]
    exact (((h1shift.hasSum.mul_left (1 + u + v)).sub
      (h2shift.hasSum.mul_left (u + v + u * v))).add
        (h3.hasSum.mul_left (u * v))).tsum_eq
  unfold firstStartRemainderDeriv3 firstStartRemainderDeriv2
    firstStartRemainderDeriv firstStartRemainder
  change (∑' n, f0 n) =
    (1 + u + v) * (∑' n, f1 n) -
      (u + v + u * v) * (∑' n, f2 n) +
        u * v * (1 + ∑' n, f3 n)
  rw [← h0split, ← h1split, ← h2split, htail]
  dsimp [f0, f1, f2, f3]
  norm_num [completeTaylorTerm, complete3, diagonal, Finset.sum_range_succ]
  ring

/-- Vieta's identities transport the normalized ODE to the original ordered
real roots. -/
theorem canonicalOrderedRealRoots_series_ode
    {a b Q root1 root2 root3 t : ℝ}
    (hroot3 : 0 < root3)
    (hsum : root1 + root2 + root3 = a + b)
    (hpair : root1 * root2 + root1 * root3 + root2 * root3 = a * b)
    (hprod : root1 * root2 * root3 = Q)
    (hu0 : 0 ≤ root1 / root3) (hu1 : root1 / root3 ≤ 1)
    (hv0 : 0 ≤ root2 / root3) (hv1 : root2 / root3 ≤ 1) :
    root3 ^ 3 * firstStartRemainderDeriv3
        (root1 / root3) (root2 / root3) (root3 * t) =
      (a + b) *
          (root3 ^ 2 * firstStartRemainderDeriv2
            (root1 / root3) (root2 / root3) (root3 * t)) -
        (a * b) *
          (root3 * firstStartRemainderDeriv
            (root1 / root3) (root2 / root3) (root3 * t)) +
        Q * (1 + firstStartRemainder
          (root1 / root3) (root2 / root3) (root3 * t)) := by
  have hne : root3 ≠ 0 := ne_of_gt hroot3
  have he1 : root3 * (1 + root1 / root3 + root2 / root3) = a + b := by
    field_simp [hne]
    nlinarith [hsum]
  have he2 : root3 ^ 2 *
      (root1 / root3 + root2 / root3 +
        (root1 / root3) * (root2 / root3)) = a * b := by
    field_simp [hne]
    nlinarith [hpair]
  have he3 : root3 ^ 3 * (root1 / root3) * (root2 / root3) = Q := by
    field_simp [hne]
    nlinarith [hprod]
  rw [firstStartRemainder_cubic_ode hu0 hu1 hv0 hv1]
  rw [← he1, ← he2, ← he3]
  ring

@[simp] theorem firstStartRemainder_zero (u v : ℝ) :
    firstStartRemainder u v 0 = 0 := by
  simp [firstStartRemainder, completeTaylorTerm]

@[simp] theorem firstStartRemainderDeriv_zero (u v : ℝ) :
    firstStartRemainderDeriv u v 0 = 0 := by
  simp [firstStartRemainderDeriv, completeTaylorTerm]

@[simp] theorem firstStartRemainderDeriv2_zero (u v : ℝ) :
    firstStartRemainderDeriv2 u v 0 = 0 := by
  simp [firstStartRemainderDeriv2, completeTaylorTerm]

/-- Any scalar solution of the canonical cubic ODE with the first-start
initial data is exactly the normalized real-root Taylor function.  This is
the uniqueness half of the canonical matrix-exponential bridge. -/
theorem canonicalOrderedRealRoots_series_eq_of_solution
    {a b Q root1 root2 root3 : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hQ : 0 ≤ Q)
    (hroot12 : root1 ≤ root2) (hroot23 : root2 ≤ root3)
    (hroot3 : 0 < root3)
    (hsum : root1 + root2 + root3 = a + b)
    (hpair : root1 * root2 + root1 * root3 + root2 * root3 = a * b)
    (hprod : root1 * root2 * root3 = Q)
    {h h1 h2 : ℝ → ℝ}
    (hh0 : ∀ t, HasDerivAt h (h1 t) t)
    (hh1 : ∀ t, HasDerivAt h1 (h2 t) t)
    (hh2 : ∀ t, HasDerivAt h2
      (Q * h t - a * b * h1 t + (a + b) * h2 t) t)
    (hinit0 : h 0 = 1) (hinit1 : h1 0 = 0) (hinit2 : h2 0 = 0) :
    h = fun t => 1 + firstStartRemainder
      (root1 / root3) (root2 / root3) (root3 * t) := by
  rcases canonicalOrderedRealRoots_admissible ha hb hQ hroot12 hroot23
      hroot3 hsum hpair hprod with ⟨hu, hv, hroot⟩
  have hu1 : root1 / root3 ≤ 1 := by
    have := hroot12.trans hroot23
    exact (div_le_one hroot3).2 this
  have hv1 : root2 / root3 ≤ 1 := (div_le_one hroot3).2 hroot23
  let F : ℝ → ℝ := fun t => 1 + firstStartRemainder
    (root1 / root3) (root2 / root3) (root3 * t)
  let F1 : ℝ → ℝ := fun t => root3 * firstStartRemainderDeriv
    (root1 / root3) (root2 / root3) (root3 * t)
  let F2 : ℝ → ℝ := fun t => root3 * (root3 * firstStartRemainderDeriv2
    (root1 / root3) (root2 / root3) (root3 * t))
  have hlin : ∀ t, HasDerivAt (fun x : ℝ => root3 * x) root3 t :=
    fun t => hasDerivAt_const_mul root3
  have hF0 : ∀ t, HasDerivAt F (F1 t) t := by
    intro t
    exact scaledFirstStart_hasDerivAt hu hu1 hv hv1
  have hF1 : ∀ t, HasDerivAt F1 (F2 t) t := by
    intro t
    have htime : HasDerivAt (fun x : ℝ => root3 * x) root3 t :=
      hasDerivAt_const_mul root3
    have hrem :=
      (firstStartRemainderDeriv_hasDerivAt hu hu1 hv hv1
        (t := root3 * t)).comp t htime
    simpa [F1, F2, Function.comp_def, mul_assoc, mul_comm,
      mul_left_comm] using (hasDerivAt_const_mul root3).comp t hrem
  have hF2 : ∀ t, HasDerivAt F2
      (Q * F t - a * b * F1 t + (a + b) * F2 t) t := by
    intro t
    have htime : HasDerivAt (fun x : ℝ => root3 * x) root3 t :=
      hasDerivAt_const_mul root3
    have hrem :=
      (firstStartRemainderDeriv2_hasDerivAt hu hu1 hv hv1
        (t := root3 * t)).comp t htime
    have hmid := (hasDerivAt_const_mul root3).comp t hrem
    have hder : HasDerivAt F2
        (root3 * (root3 * (firstStartRemainderDeriv3
          (root1 / root3) (root2 / root3) (root3 * t) * root3))) t := by
      simpa [F2, Function.comp_def] using
        (hasDerivAt_const_mul root3).comp t hmid
    convert hder using 1
    dsimp [F, F1, F2]
    have hode := canonicalOrderedRealRoots_series_ode
      (t := t) hroot3 hsum hpair hprod hu hu1 hv hv1
    nlinarith [hode]
  apply SSP.CubicODE.eq_of_cubic_ode
    (c0 := Q) (c1 := -(a * b)) (c2 := a + b) (t0 := 0)
    hh0 hh1 (fun t => by convert hh2 t using 1; ring)
    hF0 hF1 (fun t => by convert hF2 t using 1; ring)
  · simpa [F] using hinit0
  · simpa [F1] using hinit1
  · simpa [F2] using hinit2

end SSP.K3CyclicRealTail
