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

  sorry


open IsDedekindDomain.HeightOneSpectrum  WithZeroMulInt Ideal NumberField
variable {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))






/-- The norm of a maximal ideal as an element of ℝ≥0 is > 1  -/
lemma one_lt_norm : 1 < (absNorm (v.asIdeal) : NNReal) := by
  norm_cast

  sorry


/-



noncomputable instance : Valuation.RankOne (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion K v).v where
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

noncomputable instance : NormedField (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) := Valued.toNormedField (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) (WithZero (Multiplicative ℤ))

noncomputable instance : NormedDivisionRing (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) := NormedField.toNormedDivisionRing

/-- A finite place of a number field `K` is a place associated to an embedding into a completion with rescect to a maximal ideal. -/
def NumberField.FinitePlace := { w : AbsoluteValue K ℝ // ∃ φ : K →+* (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v), place φ = w }
 -/
