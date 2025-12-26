import Mathlib

noncomputable section

open IsDedekindDomain WithZeroMulInt

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K S : Type*} [Field K] [CommSemiring S]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) {b : NNReal} (hb : 1 < b) (x : R)



/-- The `v`-adic absolute value function on `K` defined as `b` raised to negative `v`-adic
valuation, for some `b` in `ℝ≥0` -/
def intAdicAbvDef := fun x ↦ toNNReal (ne_zero_of_lt hb) (v.intValuation x)

lemma isNonarchimedean_intAdicAbvDef :
    IsNonarchimedean (fun x ↦ v.intAdicAbvDef hb x) := by
  intro x y
  simp only [intAdicAbvDef]
  have h_mono := (toNNReal_strictMono hb).monotone
  rw [← h_mono.map_max]
  exact h_mono <| v.intValuation.map_add  x y

/-- The `v`-adic absolute value on `K` defined as `b` raised to negative `v`-adic
valuation, for some `b` in `ℝ≥0` -/
def intAdicAbv : AbsoluteValue R ℝ where
  toFun x := v.intAdicAbvDef hb x
  map_mul' _ _ := by simp [intAdicAbvDef]
  nonneg' _ := NNReal.zero_le_coe
  eq_zero' x := by simp [intAdicAbvDef, intValuation_def]
  add_le' _ _ := (isNonarchimedean_intAdicAbvDef v hb).add_le fun _ ↦ bot_le

/-- The `v`-adic absolute value is nonarchimedean -/
theorem isNonarchimedean_intAdicAbv :
    IsNonarchimedean (v.intAdicAbv hb) := isNonarchimedean_intAdicAbvDef v hb

theorem intAdicAbv_le_one : v.intAdicAbv hb r ≤ 1 := by
  simpa [intAdicAbv, intAdicAbvDef, toNNReal_le_one_iff hb] using intValuation_le_one v r

theorem intAdicAbv_coe_lt_one_iff : v.intAdicAbv hb r < 1 ↔ r ∈ v.asIdeal := by
  simpa [intAdicAbv, intAdicAbvDef, toNNReal_lt_one_iff hb] using intValuation_lt_one_iff_mem v r

theorem intAdicAbv_coe_eq_one_iff :
    v.intAdicAbv hb r = 1 ↔ r ∉ v.asIdeal := by
  contrapose
  rw [← v.intAdicAbv_coe_lt_one_iff hb, ne_iff_lt_iff_le]
  exact intAdicAbv_le_one v hb


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
