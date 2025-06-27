import Mathlib

namespace Polynomial

open Int

def lcmDen (p : ℚ[X]) : ℕ := p.support.lcm fun i ↦ (p.coeff i).den

--Useless?
theorem lcmDen_poly_int (p : ℤ[X]) : lcmDen (p.map (castRingHom ℚ)) = 1 := by
  simp [lcmDen, coeff_map, eq_intCast, Rat.intCast_den, Nat.cast_one]
  apply dvd_antisymm_of_normalize_eq Finset.normalize_lcm rfl _
    <| one_dvd ((map (castRingHom ℚ) p).support.lcm fun i ↦ 1)
  apply Finset.lcm_dvd
  exact fun b a ↦ one_dvd 1

theorem den_coeff_dvd_lcmDen (p : ℚ[X]) (i : ℕ) : (p.coeff i).den ∣ p.lcmDen := by
  by_cases h : i ∈ p.support
  · exact Finset.dvd_lcm h
  · simp [notMem_support_iff.mp h]

def erase_den (p : ℚ[X]) : ℤ[X] :=
  ofFn (p.natDegree + 1) (fun i ↦ (p.lcmDen) / (p.coeff i).den * (p.coeff i).num)

theorem erase_denom_eq_sum_monomial (p : ℚ[X]) : p.erase_den =
    ∑ i : Fin (p.natDegree + 1), monomial i ((lcmDen p) / (p.coeff i).den * (p.coeff i).num) := by
  simp [erase_den, ofFn_eq_sum_monomial]

theorem erase_denom_coeff (p : ℚ[X]) :
    p.erase_den.coeff = fun i ↦ (p.lcmDen) / (p.coeff i).den * (p.coeff i).num := by
  ext i
  by_cases h : i ≤ p.natDegree
  · rw [erase_den, ofFn_coeff_eq_val_of_lt _ <| Order.lt_add_one_iff.mpr h]
  · rw [not_le] at h
    simp only [erase_den, ofFn_coeff_eq_zero_of_ge _ h, zero_eq_mul, Rat.num_eq_zero]
    right
    exact coeff_eq_zero_of_natDegree_lt h

theorem erase_denom_support (p : ℚ[X]) : p.erase_den.support = p.support := by
  ext i
  simp only [mem_support_iff]
  rw [not_iff_not]
  by_cases h : i ≤ p.natDegree
  · rw [p.erase_denom_coeff]
    refine ⟨?_, fun h ↦ by simp [h] ⟩
    contrapose!
    intro h
    rw [mul_ne_zero_iff_right (Rat.num_ne_zero.mpr h), lcmDen]
    norm_cast
    apply (Nat.div_ne_zero_iff_of_dvd (Finset.dvd_lcm <| mem_support_iff.mpr h)).mpr
    refine ⟨?_, (p.coeff i).den_nz⟩
    simp [Finset.lcm_eq_zero_iff]
  · rw [not_le] at h
    simpa [erase_den, ofFn_coeff_eq_zero_of_ge _ h] using coeff_eq_zero_of_natDegree_lt h



theorem erase_denom_natDegree_eq (p : ℚ[X]) : p.erase_den.natDegree = p.natDegree := by
  apply natDegree_eq_natDegree
  simp [degree, erase_denom_support]

theorem erase_denom_leadingCoeff_of_monic {p : ℚ[X]} (hp : p.Monic) :
    p.erase_den.leadingCoeff = p.lcmDen := by
  rw [leadingCoeff]
  simp [erase_denom_coeff, erase_denom_natDegree_eq,
    coeff_natDegree, hp, lcmDen]


/- theorem foo (s : Finset β) (f : β → ℚ) : (s.gcd fun i ↦ (s.lcm fun i ↦ (f i).den) / (f i).den * (f i).num) = s.gcd fun i ↦ (f i).num := by

  sorry -/

  --apply Finset.induction_on

theorem primitive (p : ℚ[X]) (hp : p.Monic) : p.erase_den.IsPrimitive := by
  rw [isPrimitive_iff_isUnit_of_C_dvd]
  by_contra! h
  simp only [C_dvd_iff_dvd_coeff] at h
  obtain ⟨r, hr1, hr2⟩ := h
  let P := (r.natAbs).minFac
  have hPPrime : P.Prime := by
    apply Nat.minFac_prime
    rwa [ne_eq, ← isUnit_iff_natAbs_eq]
  have hPdvd1 (i : ℕ) : P ∣ (p.erase_den.coeff i).natAbs := by
    zify
    simp only [dvd_abs, hr1]
    apply dvd_trans _ <| natAbs_dvd.mpr <| hr1 i
    simpa [natCast_dvd, P] using r.natAbs.minFac_dvd
  have hPdvd2 : P ∣ p.lcmDen := by
    have := erase_denom_leadingCoeff_of_monic hp
    rw [leadingCoeff, erase_denom_natDegree_eq] at this
    zify
    rw [← this]
    exact ofNat_dvd_left.mpr <| hPdvd1 p.natDegree
  simp only [erase_denom_coeff, natAbs_mul] at hPdvd1
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

noncomputable def intMinpoly : ℤ[X] := erase_den (minpoly ℚ x)

variable [NumberField K]

--need to prove height is gal invariant
theorem equal {x : K} (hpol : ((intMinpoly x).map (algebraMap ℤ K)).Splits (RingHom.id K)) :
    (intMinpoly x).leadingCoeff =  ∏ᶠ w : FinitePlace K, max 1 (w x) := by
  have h_poleq := eq_prod_roots_of_splits_id hpol
  simp only [algebraMap_int_eq] at h_poleq
  have h (w : FinitePlace K) : w (intMinpoly x).leadingCoeff *
    (((intMinpoly x).map (algebraMap ℤ K)).roots.map (fun a ↦ max 1 (w a))).prod = 1 := by
    sorry
  sorry

end NumberField
