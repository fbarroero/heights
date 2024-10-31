import Mathlib.Data.Int.WithZero
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.FieldTheory.Finite.Basic
import Heights.WithZero

namespace Ideal

lemma one_lt_absNorm {S : Type u_1} [CommRing S] [Nontrivial S] [IsDedekindDomain S]
    [Module.Free ℤ S] {I : Ideal S } (hI_ne_top : I ≠ ⊤) (hfin_quot : 0 < absNorm I) :
    1 < absNorm I := by
  by_contra! h
  apply hI_ne_top
  rw [← absNorm_eq_one_iff]
  omega

end Ideal

open IsDedekindDomain.HeightOneSpectrum  WithZeroMulInt Ideal NumberField
variable {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- The norm of a maximal ideal as an element of ℝ≥0 is > 1  -/
lemma one_lt_norm : 1 < (absNorm (v.asIdeal) : NNReal) := by
  norm_cast
  apply one_lt_absNorm (IsPrime.ne_top v.isPrime)
  refine Nat.pos_iff_ne_zero.mpr ?_
  rw [absNorm_ne_zero_iff]
  set k := 𝓞 K ⧸ v.asIdeal
  have : Field k := Ideal.Quotient.field v.asIdeal
  have : Fintype k := Ideal.fintypeQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Fintype.finite this

lemma norm_ne_zero : (absNorm (v.asIdeal) : NNReal) ≠ 0 := ne_zero_of_lt (one_lt_norm v)

noncomputable def vadic_abv : AbsoluteValue K ℝ where
  toFun := fun x ↦ (toNNReal (norm_ne_zero v) (v.valuation x))
  map_mul' := by
    intro x y
    simp_all only [_root_.map_mul, NNReal.coe_mul]
  nonneg' := fun x ↦ NNReal.zero_le_coe
  eq_zero' := by
    intro x
    simp_all only [NNReal.coe_eq_zero, map_eq_zero]
  add_le' := by
    intro x y
    simp only
    norm_cast
    -- the triangular inequality is implied by the ultrametric one
    apply le_trans _ <| max_le_add_of_nonneg (by simp only [zero_le]) (by simp only [zero_le])
    have h_mono := StrictMono.monotone (WithZeroMulInt.toNNReal_strictMono (one_lt_norm v))
    rw [← Monotone.map_max h_mono] --max goes inside withZeroMultIntToNNReal
    exact h_mono (Valuation.map_add v.valuation x y)

theorem vadic_abv_def : vadic_abv v x = (toNNReal (norm_ne_zero v) (v.valuation x)) := rfl




noncomputable instance i1 : Valuation.RankOne (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion K v).v where
  hom := {
    toFun := toNNReal (norm_ne_zero v)
    map_zero' := rfl
    map_one' := rfl
    map_mul' := MonoidWithZeroHom.map_mul (toNNReal (norm_ne_zero v))
  }
  strictMono' := WithZeroMulInt.toNNReal_strictMono (one_lt_norm v)
  nontrivial' := by
    have : ∃ x ∈ v.asIdeal, x ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    rcases this with ⟨x, hx⟩
    use (x : K)
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : K)]
    constructor
    · simp_all only [ne_eq, map_eq_zero, NoZeroSMulDivisors.algebraMap_eq_zero_iff, not_false_eq_true]
    · apply ne_of_lt
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_intValuationDef, IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd]
      simp_all only [ne_eq, Ideal.dvd_span_singleton]

noncomputable instance i2 : NormedField (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :=
    Valued.toNormedField (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) (WithZero (Multiplicative ℤ))

--noncomputable instance : NormedDivisionRing (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) := NormedField.toNormedDivisionRing

/-- A finite place of a number field `K` is a place associated to an embedding into a completion with rescect to a maximal ideal. -/
def NumberField.FinitePlace := { w : AbsoluteValue K ℝ //
    ∃ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
    ∃ φ : K →+* (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v), place φ = w }

/-- Return the finite place defined by a maximal ideal `v`. -/
noncomputable def NumberField.FinitePlace.mk (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : @NumberField.FinitePlace K _ _ where
  val := vadic_abv v
  property := by
    use v
    let f : K →+* adicCompletion K v := {
      toFun := fun x ↦ x
      map_one' := rfl
      map_mul' := by
        simp only
        intro x y
        norm_cast
      map_zero' := rfl
      map_add' := by
        simp only
        intro x y
        norm_cast
    }
    use f
    have a := i1 v
    have b := i2 v
    ext x
    simp only [place_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, f, norm,
      NormedField.toNormedDivisionRing]
    unfold norm
    unfold NormedField.toNorm
    simp [i2]



    /-
    simp only [place_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, vadic_abv_def, f]



    --unfold NormedDivisionRing.toNorm
    unfold norm
    unfold NormedDivisionRing.toNorm
    --simp_all only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, f]
    unfold NormedField.toNormedDivisionRing
    unfold instNormedFieldAdicCompletionRingOfIntegers_heights
     -/

    sorry
