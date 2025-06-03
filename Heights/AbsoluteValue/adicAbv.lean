import Mathlib

noncomputable section

open IsDedekindDomain WithZeroMulInt

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K S : Type*} [Field K] [CommSemiring S]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

--PRd
/- theorem adicAbv_coe_le_one {b : NNReal} (hb : 1 < b) (r : R) :
    v.adicAbv hb (algebraMap R K r) ≤ 1 := by
  simpa [adicAbv, adicAbvDef, toNNReal_le_one_iff hb] using valuation_le_one v r -/

--PRd
/- theorem adicAbv_coe_lt_one_iff {b : NNReal} (hb : 1 < b) (r : R) :
    v.adicAbv hb (algebraMap R K r) < 1 ↔ r ∈ v.asIdeal := by
  simpa [adicAbv, adicAbvDef, toNNReal_lt_one_iff hb] using valuation_lt_one_iff_mem v r -/

end IsDedekindDomain.HeightOneSpectrum

end
