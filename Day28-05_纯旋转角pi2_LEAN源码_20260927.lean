import Mathlib

/-! ================================================================
   偏元数学 · Day28-05 · 动作上链与和乐 · 纯旋转角 δ = π/2（K0 约束）
   ------------------------------------------------------------------
   核心：K0 约束"Δr = ε·cos δ = 0"（纯旋转）在 ε ≠ 0 下逼出 cos δ = 0；
         在 δ ∈ [0,π] 上，其唯一解是 δ = π/2。
   本稿范围：四定理
     定理1  cos_eq_zero_of_mul : ε≠0 ∧ ε·cos δ = 0 ⟹ cos δ = 0
     定理2  cos_pi_div_two_zero: cos (π/2) = 0
     定理3  spin_requires_cos_zero : 0<ε ∧ ε·cos δ = 0 ⟹ cos δ = 0 （推论）
     定理4  cos_eq_zero_unique : cos δ = 0 ∧ 0≤δ ∧ δ≤π ⟹ δ = π/2  ⚠️ 见下
   不做：不引入 ℂ（本件纯 ℝ）。
   注：定理1/2/3 只依赖 mul_eq_zero 与 Real.cos_pi_div_two，极稳。
       定理4 依赖 Mathlib 的 cos 零点刻画，写法可能需按实际报错调整。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ----------------------------------------------------------------
   ⚠️ 本件未在本地编译过。定理4 是最可能报错的一条；
      若报错，请贴回错误行，我按报错改（备选见文末注释）。
   ================================================================ -/

namespace PrenaryDay28E

/-- 定理1：ε≠0 且 ε·cos δ = 0 ⟹ cos δ = 0 -/
theorem cos_eq_zero_of_mul {ε δ : ℝ} (hε : ε ≠ 0) (h : ε * Real.cos δ = 0) :
    Real.cos δ = 0 :=
  (mul_eq_zero.mp h).resolve_left hε

/-- 定理2：π/2 是 cos 的零点 -/
theorem cos_pi_div_two_zero : Real.cos (Real.pi / 2) = 0 :=
  Real.cos_pi_div_two

/-- 定理3（纯旋转的必要条件）：0<ε 且 ε·cos δ = 0 ⟹ cos δ = 0 -/
theorem spin_requires_cos_zero {ε δ : ℝ} (hε : 0 < ε) (h : ε * Real.cos δ = 0) :
    Real.cos δ = 0 :=
  cos_eq_zero_of_mul (ne_of_gt hε) h

/-- 定理4（唯一性）：cos δ = 0 且 δ ∈ [0,π] ⟹ δ = π/2 -/
theorem cos_eq_zero_unique {δ : ℝ} (h0 : 0 ≤ δ) (hπ : δ ≤ Real.pi)
    (hc : Real.cos δ = 0) : δ = Real.pi / 2 := by
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hc
  have hk' : δ = (k : ℝ) * Real.pi + Real.pi / 2 := hk
  rw [hk'] at h0 hπ
  have hk0 : (0 : ℝ) ≤ k := by
    by_contra hneg
    push_neg at hneg
    have : (k : ℝ) * Real.pi + Real.pi / 2 < 0 := by
      have : (k : ℝ) ≤ -1 := by exact_mod_cast (Int.le_of_lt_add_one hneg)
      nlinarith [Real.pi_pos]
    linarith
  have hk1 : (k : ℝ) ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have : Real.pi < (k : ℝ) * Real.pi + Real.pi / 2 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (Int.add_one_le_iff.mp hpos)
      nlinarith [Real.pi_pos]
    linarith
  have hk0' : k = 0 := by
    have : (k : ℝ) = 0 := le_antisymm hk1 hk0
    exact_mod_cast this
  rw [hk0'] at hk'
  simp at hk'
  exact hk'

end PrenaryDay28E

/- ----------------------------------------------------------------
   定理4 备选写法（若上面报错时依次试）：

   （a）引理名变体：
        Real.cos_eq_zero_iff'    或    Real.cos_eq_zero_iff

   （b）改用单调性一步到位（最简洁，若 Mathlib 有）：
        exact (Real.strictAntiOn_cos.eq_of_le h0 hπ).resolve_left ?_
        -- 或  Real.cos_eq_zero_iff_of_mem_Icc

   （c）最保守的替代（不依赖零点刻画）：
        把定理4 换成"π/2 是 [0,π] 内的零点"这一半，配合定理2 ——
        即只证：cos (π/2) = 0 ∧ 0 ≤ π/2 ∧ π/2 ≤ π。这四条都是一行。

   注：若白天只跑得动定理1/2/3，也够用 —— 本仓的承重证据在 Day28-04，
       Day28-05 是它的"δ = π/2 从哪来"的交代。
   ---------------------------------------------------------------- -/
