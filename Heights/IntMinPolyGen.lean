import Mathlib

variable {R K : Type*} [DecidableEq R] [CommSemiring R] [CommMonoidWithZero R] [IsCancelMulZero R]
[NormalizedGCDMonoid R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq K]

namespace Finset

variable (s : Finset K)

variable (R) in
noncomputable def lcmDen : R := s.lcm (fun x ↦
  let q := (IsLocalization.sec (nonZeroDivisors R) x)
  --normalize <|
  Classical.choose (GCDMonoid.gcd_dvd_right q.1 q.2))

--#eval ((singleton 1 : Finset ℚ)).lcmDen ℤ

/- theorem aa (x : ℤ) : normalize x = x.natAbs := by
  simp [normalize, normUnit, abs]
  by_cases h : 0 ≤ x
  simp [h]
  simp [h]
  omega -/

theorem aux (x : ℚ) (q : ℤ × ↥(nonZeroDivisors ℤ)) (d : ℤ) (hq : q = (IsLocalization.sec (nonZeroDivisors ℤ) x))
  (hd : d = Classical.choose (GCDMonoid.gcd_dvd_right q.1 q.2)) :
  Associated d x.den := by
  have : x * q.2 = q.1 := by
    have := IsLocalization.sec_spec (nonZeroDivisors ℤ) x
    simp_all
  have : x.num * q.2 = x.den * q.1 := by
    qify
    rw [← this, ← Rat.den_mul_eq_num]
    grind
  let g := GCDMonoid.gcd q.1 (q.2 : ℤ)
  have hd' : q.2 = g * d := by grind
  let n := Classical.choose (GCDMonoid.gcd_dvd_left q.1 q.2)
  have hn : q.1 = g * n := by grind
  rw [hd', hn] at this

  have hgnezero : g ≠ 0 := by simp [g]
  have : g * (x.den * n) = g * (x.num * d) := by grind
  rw [mul_right_inj' hgnezero] at this
  rw [← dvd_dvd_iff_associated]
  have t1 : d ∣ x.den * n := by exact Dvd.intro_left x.num (id (Eq.symm this))
  have t2 : (x.den : ℤ ) ∣ x.num * d := by exact Dvd.intro n this
  have hcop := isCoprime_div_gcd_div_gcd (p := q.1) (q := q.2)
  have e1 : (q.1 / GCDMonoid.gcd q.1 ↑q.2) = n := by
    nth_rw 1 [hn]
    simp [g]
  have e2 : (q.2 / GCDMonoid.gcd q.1 ↑q.2) = d := by
    nth_rw 1 [hd']
    simp [g]
  simp at hcop
  rw [e1, e2] at hcop
  constructor
  · apply Int.dvd_of_dvd_mul_left_of_gcd_one t1
    exact Int.isCoprime_iff_gcd_eq_one.mp (id (IsCoprime.symm hcop))
  · apply Int.dvd_of_dvd_mul_right_of_gcd_one t2
    have := x.reduced
    rw [Nat.coprime_iff_gcd_eq_one] at this
    rw [← this, Int.gcd_eq_natAbs]
    exact Nat.gcd_comm _ _


theorem foo (s : Finset ℚ) : s.lcmDen ℤ = s.lcm (fun x ↦ (x.den : ℤ)) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [lcmDen]
  | insert a s has hind =>
    --simp [lcmDen]
    simp [← hind, lcmDen]
    apply lcm_eq_of_associated_left
    exact
      aux a (IsLocalization.sec (nonZeroDivisors ℤ) a) (Classical.choose (lcmDen._proof_1 ℤ a)) rfl
        rfl


theorem lcmDen_cast (p : Finset R) : (p.image (algebraMap R K)).lcmDen R = 1 := by
  simp [lcmDen]
  have (x : R) : (IsLocalization.sec (nonZeroDivisors R) (algebraMap R K x)).2 = 1 := by
    --Localization.map_isUnit_of_le
    sorry
  sorry

end Finset

/- namespace Polynomial

variable (p : K[X])

variable (R) in
noncomputable def lcmDen := p.coeffs.lcmDen R

theorem foo : p.lcmDen R = p.support.lcm (α := R) fun i ↦ (IsLocalization.sec (nonZeroDivisors R) (p.coeff i)).2 := by
  simp [lcmDen, Finset.lcmDen]
  simp [Finset.lcm_def]
  congr

  sorry

end Polynomial -/
