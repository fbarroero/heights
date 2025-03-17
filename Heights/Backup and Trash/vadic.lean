import Mathlib.Data.Int.WithZero
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.FieldTheory.Finite.Basic

import Heights.WithZero

open NumberField
variable {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

open IsDedekindDomain.HeightOneSpectrum  WithZeroMulInt

/-- The norm of a maximal ideal as an element of ℝ≥0 is > 1  -/
lemma one_lt_norm : 1 < (Nat.card <| 𝓞 K ⧸ v.asIdeal : NNReal) := by
  set k := 𝓞 K ⧸ v.asIdeal
  have : Field k := Ideal.Quotient.field v.asIdeal
  have : Fintype k := Ideal.fintypeQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  rcases FiniteField.card' k with ⟨p, n, hp, hcard⟩
  simp only [Nat.card_eq_fintype_card, hcard]
  norm_cast
  refine Nat.one_lt_pow (PNat.ne_zero n) (Nat.Prime.one_lt hp)

/-- The norm of a maximal ideal as an element of ℝ≥0 is non zero   -/
lemma norm_ne_zero : (Nat.card <| 𝓞 K ⧸ v.asIdeal : NNReal) ≠ 0 := ne_zero_of_lt (one_lt_norm v)


/-- The Padic norm with respect to a maximal ideal.  -/
noncomputable def PadicNorm : K → ℝ := fun x =>
    toNNReal (norm_ne_zero v) ((IsDedekindDomain.HeightOneSpectrum.valuation v) x)

theorem PadicNorm_def (x : K) : PadicNorm v x =
    toNNReal (norm_ne_zero v) ((IsDedekindDomain.HeightOneSpectrum.valuation v) x) :=
    rfl

lemma Padic_norm_zero : PadicNorm v 0 = 0 := by
  rw [PadicNorm_def]
  exact_mod_cast toNNReal_pos_apply _ (Valuation.map_zero v.valuation)

theorem Padic_norm_int_le_one (x : 𝓞 K) : PadicNorm v x ≤ 1 := by
  by_cases h : x = 0
  · rw [h]
    simp only [map_zero, Padic_norm_zero]
    exact zero_le_one' ℝ
  · rw [PadicNorm_def]
    simp only [NNReal.coe_le_one]
    rw [le_one (one_lt_norm v)]
    exact valuation_le_one v x

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
