import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Instances.NNReal.Lemmas

-- Not used, but included for completeness
theorem NNReal.iSup_rpow {ι : Sort*} [Nonempty ι] (f : ι → NNReal) {r : ℝ} (hr : 0 ≤ r) :
    (⨆ i, f i) ^ r = ⨆ i, f i ^ r := by
  obtain hr | hr := hr.eq_or_gt
  · simp [hr]
  · exact (NNReal.orderIsoRpow r hr).map_ciSup' _

theorem ENNReal.iSup_rpow {ι : Sort*} [Nonempty ι] (f : ι → ENNReal) {r : ℝ} (hr : 0 ≤ r) :
    (⨆ i, f i) ^ r = ⨆ i, f i ^ r := by
  obtain hr | hr := hr.eq_or_gt
  · simp [hr]
  · exact (ENNReal.orderIsoRpow r hr).map_ciSup' _
