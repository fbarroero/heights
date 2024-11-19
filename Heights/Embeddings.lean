import Mathlib.Data.Int.WithZero
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Norm.absNorm
import Mathlib.Topology.Algebra.Valued.NormedValued

open IsDedekindDomain.HeightOneSpectrum  WithZeroMulInt Ideal NumberField

namespace NumberField

section absoluteValue

variable {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- The norm of a maximal ideal as an element of ℝ≥0 is > 1  -/
lemma one_lt_norm : 1 < (absNorm v.asIdeal : NNReal) := by
  norm_cast
  by_contra! h
  apply IsPrime.ne_top v.isPrime
  rw [← absNorm_eq_one_iff]
  have : 0 < absNorm v.asIdeal := by
    rw [Nat.pos_iff_ne_zero, absNorm_ne_zero_iff]
    set k := 𝓞 K ⧸ v.asIdeal
    have : Field k := Ideal.Quotient.field v.asIdeal
    have : Fintype k := Ideal.fintypeQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    exact Fintype.finite this
  omega

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

end NumberField

section FinitePlace
variable {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

def embedding : K →+* (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :=
    @UniformSpace.Completion.coeRingHom K _ v.adicValued.toUniformSpace _ _

noncomputable instance instRankOneValuedAdicCompletion : Valuation.RankOne (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion K v).v where
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

noncomputable instance instNormedFieldValuedAdicCompletion : NormedField (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :=
    Valued.toNormedField (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) (WithZero (Multiplicative ℤ))

/-- A finite place of a number field `K` is a place associated to an embedding into a completion with rescect to a maximal ideal. -/
def NumberField.FinitePlace (K : Type*) [Field K] [NumberField K] := { w : AbsoluteValue K ℝ //
    ∃ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)), place (embedding v) = w }

/-- Return the finite place defined by a maximal ideal `v`. -/
noncomputable def NumberField.FinitePlace.mk (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    NumberField.FinitePlace K := ⟨place (embedding v), ⟨v, rfl⟩⟩

theorem NumberField.FinitePlace.norm_def (x : K) : ‖(embedding v) x‖ = toNNReal (norm_ne_zero v) (v.valuation x) := by
  by_cases h : x = 0
  · subst h
    simp_all only [map_zero, norm_zero, NNReal.coe_zero]
  · --unfold embedding
    simp only [NormedField.toNorm, instNormedFieldValuedAdicCompletion, Valued.toNormedField,
      instFieldAdicCompletion, Valued.norm, Valuation.RankOne.hom, MonoidWithZeroHom.coe_mk,
      ZeroHom.coe_mk, embedding, UniformSpace.Completion.coeRingHom, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, Valued.valuedCompletion_apply, NNReal.coe_inj]
    rfl

theorem norm_le_one (x : 𝓞 K) : ‖(embedding v) x‖ ≤ 1 := by
  rw [NumberField.FinitePlace.norm_def, NNReal.coe_le_one,
    WithZeroMulInt.toNNReal_le_one_iff (one_lt_norm v)]
  exact valuation_le_one v x

theorem norm_eq_one_iff_not_mem (x : 𝓞 K) : ‖(embedding v) x‖ = 1 ↔ x ∉ v.asIdeal := by
  rw [NumberField.FinitePlace.norm_def, NNReal.coe_eq_one,
    WithZeroMulInt.toNNReal_eq_one_iff (v.valuation (x : K))
    (norm_ne_zero v) (Ne.symm (ne_of_lt (one_lt_norm v))), @valuation_eq_intValuationDef,
    ← @dvd_span_singleton, ← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd, not_lt]
  exact Iff.symm (LE.le.ge_iff_eq (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v x))

theorem norm_lt_one_iff_mem (x : 𝓞 K) : ‖(embedding v) x‖ < 1 ↔ x ∈ v.asIdeal := by
  rw [NumberField.FinitePlace.norm_def, NNReal.coe_lt_one,
    WithZeroMulInt.toNNReal_lt_one_iff (one_lt_norm v), @valuation_eq_intValuationDef,
    IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd]
  exact dvd_span_singleton

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
theorem apply (x : K) : (mk v) x =  ‖embedding v x‖ := rfl

noncomputable def maximal_ideal (w : FinitePlace K) : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := w.2.choose

/-- For a finite place `w`, return a maximal ideal `v` such that `w = finite_place v` . -/
@[simp]
theorem mk_max_ideal (w : FinitePlace K) : mk (maximal_ideal w) = w := Subtype.ext w.2.choose_spec

theorem norm_embedding_eq (w : FinitePlace K) (x : K) :
    ‖(embedding (maximal_ideal w)) x‖ = w x := by
  have h : w x = (mk (maximal_ideal w)) x := by simp only [mk_max_ideal]
  rw [h]
  rfl

theorem eq_iff_eq (x : K) (r : ℝ) : (∀ w : FinitePlace K, w x = r) ↔
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(embedding v) x‖ = r :=
    Set.forall_subtype_range_iff

theorem le_iff_le (x : K) (r : ℝ) : (∀ w : FinitePlace K, w x ≤ r) ↔
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(embedding v) x‖ ≤ r :=
    Set.forall_subtype_range_iff

theorem pos_iff {w : FinitePlace K} {x : K} : 0 < w x ↔ x ≠ 0 := AbsoluteValue.pos_iff w.1

@[simp]
theorem mk_eq_iff {v₁ v₂ : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} : mk v₁ = mk v₂ ↔ v₁ = v₂ := by
  refine ⟨?_,  fun a ↦ by rw [a]⟩
  contrapose!
  intro h
  rw [@DFunLike.ne_iff]
  have : ∃ x : 𝓞 K, x ∈ v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra!
    apply h
    exact IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
      (IsMaximal.eq_of_le (isMaximal v₁) IsPrime.ne_top' this)
  rcases this with ⟨x, hx1, hx2⟩
  use x
  simp only [apply]
  rw [← norm_lt_one_iff_mem ] at hx1
  rw [← norm_eq_one_iff_not_mem] at hx2
  linarith

theorem mulSupport_Finite {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    (Function.mulSupport fun w : FinitePlace K => w x).Finite := by
  have (w : FinitePlace K) : w x ≠ 1 ↔ w x < 1 := by
    sorry
  simp_rw [Function.mulSupport, this, ← norm_embedding_eq, norm_lt_one_iff_mem,
    ← Ideal.dvd_span_singleton]
  have h : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ span {x}}.Finite := by
    apply Ideal.finite_factors
    simp_all only [ne_eq, ne_iff_lt_iff_le, Submodule.zero_eq_bot, span_singleton_eq_bot, not_false_eq_true]
  have h_inj : Set.InjOn (fun w : FinitePlace K ↦ maximal_ideal w) {x_1 | x_1.maximal_ideal.asIdeal ∣ span {x}} := by
    refine Function.Injective.injOn ?h
    intro w₁ w₂
    simp only
    intro h
    rw [← mk_max_ideal w₁, ← mk_max_ideal w₂]
    exact congrArg mk h
  apply Set.Finite.of_finite_image _ h_inj
  have h_subs : ((fun (w : FinitePlace K) ↦ w.maximal_ideal) '' {x_1 : FinitePlace K | x_1.maximal_ideal.asIdeal ∣ span {x}}) ⊆ { v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ span {x}} := by
    intro w h
    simp_all only [ne_eq, ne_iff_lt_iff_le, dvd_span_singleton, Set.mem_image, Set.mem_setOf_eq]
    obtain ⟨w_1, h⟩ := h
    obtain ⟨left, right⟩ := h
    subst right
    simp_all only
  apply Set.Finite.subset _ h_subs
  exact h

end NumberField.FinitePlace
