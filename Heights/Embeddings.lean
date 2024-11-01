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

section absoluteValue

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

end absoluteValue

section FinitePlace
variable {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

noncomputable instance instinstRankOneValuedAdicCompletion : Valuation.RankOne (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion K v).v where
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

noncomputable instance instinstNormedFieldValuedAdicCompletion : NormedField (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :=
    Valued.toNormedField (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) (WithZero (Multiplicative ℤ))

/-- A finite place of a number field `K` is a place associated to an embedding into a completion with rescect to a maximal ideal. -/
def NumberField.FinitePlace (K : Type*) [Field K] [NumberField K] := { w : AbsoluteValue K ℝ //
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
    ext x
    simp only [place_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, f, norm,
      NormedField.toNormedDivisionRing, instinstNormedFieldValuedAdicCompletion, instinstRankOneValuedAdicCompletion, Valued.toNormedField, Valued.norm, Valued.valuedCompletion_apply]
    norm_cast

end FinitePlace
namespace NumberField.FinitePlace
open NumberField
variable {K : Type*} [Field K] [NumberField K]

instance : FunLike (FinitePlace K) K ℝ where
  coe w x := w.1 x
  coe_injective' _ _ h := Subtype.eq (AbsoluteValue.ext fun x => congr_fun h x)

instance : MonoidWithZeroHomClass (FinitePlace K) K ℝ where
  map_mul w _ _ := w.1.map_mul _ _
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

instance : NonnegHomClass (FinitePlace K) K ℝ where
  apply_nonneg w _ := w.1.nonneg _

@[simp]
theorem apply (x : K) : (mk v) x = vadic_abv v x := rfl

noncomputable def maximal_ideal (w : FinitePlace K) : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := Exists.choose w.2

/-- For a finite place `w`, return an embedding `φ` such that `w = finite_place φ` . -/
noncomputable def embedding (w : FinitePlace K) : K →+* (IsDedekindDomain.HeightOneSpectrum.adicCompletion K (maximal_ideal w)) := Exists.choose (Exists.choose_spec w.2)

/- @[simp]
theorem mk_max_ideal (w : FinitePlace K) : mk (maximal_ideal w) = w := by

  have := w.2.choose_spec
  apply Subtype.ext

  have := Exists.choose this
  rename_i this_1
  obtain ⟨w_1, h⟩ := this_1
  rw [← h]
  ext x
  simp_all [apply x]
  push_cast
  rw [apply x]
  sorry

   -/


--Subtype.ext w.2.choose_spec


/- theorem norm_embedding_eq (w : FinitePlace K) (x : K) :
    ‖(embedding w) x‖ = w x := by
  nth_rewrite 2 [← mk_embedding w]
  rfl -/
/-
theorem eq_iff_eq (x : K) (r : ℝ) : (∀ w : FinitePlace K, w x = r) ↔ ∀ φ : K →+* ℂ, ‖φ x‖ = r :=
  ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩

theorem le_iff_le (x : K) (r : ℝ) : (∀ w : InfinitePlace K, w x ≤ r) ↔ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r :=
  ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩ -/

theorem pos_iff {w : FinitePlace K} {x : K} : 0 < w x ↔ x ≠ 0 := AbsoluteValue.pos_iff w.1

@[simp]
theorem mk_eq_iff {v₁ v₂ : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} : mk v₁ = mk v₂ ↔ v₁ = v₂ := by
  constructor
  · intro h

    sorry
  · intro a
    subst a
    simp_all only

end NumberField.FinitePlace
