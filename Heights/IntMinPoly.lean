import Mathlib

namespace Polynomial

open Int

/-- The least common multiple of the denominators of the coefficients of a polynomial over `ℚ`. -/
def lcmDen (p : ℚ[X]) : ℕ := p.support.lcm fun i ↦ (p.coeff i).den

open Finset in
/-- The least common multiple of the denominators of the coefficients of a polynomial over `ℤ` is 1.
-/
theorem lcmDen_poly_int (p : ℤ[X]) : (p.map (castRingHom ℚ)).lcmDen = 1 := by
  simp only [lcmDen, coeff_map, eq_intCast, Rat.den_intCast]
  apply dvd_antisymm_of_normalize_eq normalize_lcm rfl _ <| one_dvd _
  exact lcm_dvd <| fun b a ↦ one_dvd 1

theorem den_coeff_dvd_lcmDen (p : ℚ[X]) (i : ℕ) : (p.coeff i).den ∣ p.lcmDen := by
  by_cases h : i ∈ p.support
  · exact Finset.dvd_lcm h
  · simp [notMem_support_iff.mp h]

def eraseDen (p : ℚ[X]) : ℤ[X] :=
  ofFn (p.natDegree + 1) (fun i ↦ (p.lcmDen) / (p.coeff i).den * (p.coeff i).num)

theorem eraseDen_eq_sum_monomial (p : ℚ[X]) : p.eraseDen =
    ∑ i : Fin (p.natDegree + 1), monomial i ((lcmDen p) / (p.coeff i).den * (p.coeff i).num) := by
  simp [eraseDen, ofFn_eq_sum_monomial]

theorem eraseDen_coeff (p : ℚ[X]) :
    p.eraseDen.coeff = fun i ↦ (p.lcmDen) / (p.coeff i).den * (p.coeff i).num := by
  ext i
  by_cases h : i ≤ p.natDegree
  · rw [eraseDen, ofFn_coeff_eq_val_of_lt _ <| Order.lt_add_one_iff.mpr h]
  · rw [not_le] at h
    simp only [eraseDen, ofFn_coeff_eq_zero_of_ge _ h, zero_eq_mul, Rat.num_eq_zero]
    right
    exact coeff_eq_zero_of_natDegree_lt h

theorem eraseDen_support (p : ℚ[X]) : p.eraseDen.support = p.support := by
  ext i
  simp only [mem_support_iff]
  rw [not_iff_not]
  by_cases h : i ≤ p.natDegree
  · rw [p.eraseDen_coeff]
    refine ⟨?_, fun h ↦ by simp [h] ⟩
    contrapose!
    intro h
    rw [mul_ne_zero_iff_right (Rat.num_ne_zero.mpr h), lcmDen]
    norm_cast
    apply (Nat.div_ne_zero_iff_of_dvd (Finset.dvd_lcm <| mem_support_iff.mpr h)).mpr
    refine ⟨?_, (p.coeff i).den_nz⟩
    simp [Finset.lcm_eq_zero_iff]
  · rw [not_le] at h
    simpa [eraseDen, ofFn_coeff_eq_zero_of_ge _ h] using coeff_eq_zero_of_natDegree_lt h



theorem eraseDen_natDegree_eq (p : ℚ[X]) : p.eraseDen.natDegree = p.natDegree := by
  apply natDegree_eq_natDegree
  simp [degree, eraseDen_support]

theorem eraseDen_leadingCoeff_of_monic {p : ℚ[X]} (hp : p.Monic) :
    p.eraseDen.leadingCoeff = p.lcmDen := by
  rw [leadingCoeff]
  simp [eraseDen_coeff, eraseDen_natDegree_eq,
    coeff_natDegree, hp, lcmDen]


/- theorem foo (s : Finset β) (f : β → ℚ) : (s.gcd fun i ↦ (s.lcm fun i ↦ (f i).den) / (f i).den * (f i).num) = s.gcd fun i ↦ (f i).num := by

  sorry -/

  --apply Finset.induction_on

theorem primitive (p : ℚ[X]) (hp : p.Monic) : p.eraseDen.IsPrimitive := by
  rw [isPrimitive_iff_isUnit_of_C_dvd]
  by_contra! h
  simp only [C_dvd_iff_dvd_coeff] at h
  obtain ⟨r, hr1, hr2⟩ := h
  let P := (r.natAbs).minFac
  have hPPrime : P.Prime := by
    apply Nat.minFac_prime
    rwa [ne_eq, ← isUnit_iff_natAbs_eq]
  have hPdvd1 (i : ℕ) : P ∣ (p.eraseDen.coeff i).natAbs := by
    zify
    simp only [dvd_abs]
    apply dvd_trans _ <| natAbs_dvd.mpr <| hr1 i
    simpa [natCast_dvd, P] using r.natAbs.minFac_dvd
  have hPdvd2 : P ∣ p.lcmDen := by
    have := eraseDen_leadingCoeff_of_monic hp
    rw [leadingCoeff, eraseDen_natDegree_eq] at this
    zify
    rw [← this]
    exact ofNat_dvd_left.mpr <| hPdvd1 p.natDegree
  simp only [eraseDen_coeff, natAbs_mul] at hPdvd1
  norm_cast at hPdvd1
  conv at hPdvd1 => ext i; norm_cast; rw [Nat.Prime.dvd_mul hPPrime]
  have hPdvdden_of (i : ℕ): ¬(P ∣ p.lcmDen / (p.coeff i).den) → P ∣ (p.coeff i).num.natAbs := by
    intro h
    specialize hPdvd1 i
    simp_all

  have hPdvnum_of (i : ℕ) : ¬(P ∣ p.lcmDen / (p.coeff i).den) → P ∣ (p.coeff i).den := by
    have hlcm := den_coeff_dvd_lcmDen p i
    contrapose!
    intro h
    refine (Nat.dvd_div_iff_mul_dvd hlcm).mpr ?_
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ hlcm hPdvd2
    rwa [Nat.Prime.dvd_iff_not_coprime hPPrime, Decidable.not_not,  Nat.coprime_comm] at h


  have hP6 (i : ℕ) : P ∣ p.lcmDen / (p.coeff i).den := by
    by_contra! h
    specialize hPdvdden_of i h
    specialize hPdvnum_of i h
    simp_all [Nat.Coprime.coprime_dvd_left hPdvdden_of (p.coeff i).reduced, Nat.Prime.dvd_iff_not_coprime hPPrime]
  have hP7 (i : ℕ) : (p.coeff i).den ∣ p.lcmDen / P := by
    specialize hP6 i
    refine Nat.dvd_div_of_mul_dvd ?_
    rw [mul_comm, ← Nat.dvd_div_iff_mul_dvd (den_coeff_dvd_lcmDen p i)]
    exact hP6
  have hP8 : p.lcmDen ∣ p.lcmDen / P := by
    apply Finset.lcm_dvd
    intro i hi
    exact hP7 i
  have hlcm_pos : 0 < p.lcmDen := by
    simp [lcmDen, Nat.pos_iff_ne_zero, Finset.lcm_eq_zero_iff]
  rw [Nat.dvd_div_iff_mul_dvd hPdvd2, mul_comm, ← Nat.dvd_div_iff_mul_dvd (Nat.dvd_refl p.lcmDen),
    Nat.div_self hlcm_pos] at hP8
  simp_all [Nat.Prime.ne_one]

end Polynomial

namespace NumberField

variable {K : Type*} [Field K] [Algebra ℚ K] (x : K) (hx : IsIntegral ℚ x)

open Polynomial

noncomputable def intMinpoly : ℤ[X] := eraseDen (minpoly ℚ x)

variable [NumberField K]

--need to prove height is gal invariant
theorem equal {x : K} (hpol : ((intMinpoly x).map (algebraMap ℤ K)).Splits /- (RingHom.id K) -/) :
    (intMinpoly x).leadingCoeff =  ∏ᶠ w : FinitePlace K, max 1 (w x) := by
  --have h_poleq := eq_prod_roots_of_splits_id hpol
  --simp only [algebraMap_int_eq] at h_poleq
  have h (w : FinitePlace K) : w (intMinpoly x).leadingCoeff *
    (((intMinpoly x).map (algebraMap ℤ K)).roots.map (fun a ↦ max 1 (w a))).prod = 1 := by
    sorry
  sorry

end NumberField
