import Mathlib.Analysis.RCLike.Basic

theorem RCLike.norm_I {K : Type*} [RCLike K] :
    ‖(RCLike.I : K)‖ = if RCLike.I ≠ (0 : K) then 1 else 0 := by
  split_ifs with h
  · apply RCLike.norm_I_of_ne_zero h
  · push Not at h
    simpa
