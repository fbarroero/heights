import Mathlib

noncomputable section

open IsDedekindDomain WithZeroMulInt

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K S : Type*} [Field K] [CommSemiring S]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

lemma isNonanchimedean_toNNNReal_valuation {b : NNReal} (hb : 1 < b) :
    IsNonarchimedean (fun x ↦ toNNReal (ne_zero_of_lt hb) (v.valuation K x)) := by
  intro x y
  have h_mono := (toNNReal_strictMono hb).monotone
  rw [← h_mono.map_max]
  exact h_mono ((v.valuation _).map_add x y)

def adicAbv {b : NNReal} (hb : 1 < b) : AbsoluteValue K ℝ where
  toFun x := toNNReal (ne_zero_of_lt hb) (v.valuation K x)
  map_mul' _ _ := by simp
  nonneg' _ := NNReal.zero_le_coe
  eq_zero' _ := by simp
  add_le' x y := (isNonanchimedean_toNNNReal_valuation v hb).add_le (fun x ↦ zero_le ((toNNReal (ne_zero_of_lt hb)) (v.valuation K x)))

end IsDedekindDomain.HeightOneSpectrum

end
