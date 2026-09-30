import Mathlib

/-! ================================================================
   偏元数学 · Day28-17 · 量的偏好 · 相对尺度与对称性（K1／K2）
   ------------------------------------------------------------------
   核心：V1.2 §9 的"偏好量"改用**相对尺度**（以区间 (0,δ₀) 为单位），
         得无量纲量 Pref(δ₀) = 放大侧余量 − 缩小侧余量 = 1 − 2/δ₀；
         并落定"对称 ⟹ 中心量为 0"这一形态在两侧的实例：
           · 缩放侧：两档等宽 ⟺ Pref = 0 ⟺ δ₀ = 2（不动点落在中点）
           · 方向侧：对径点成对 ⟹ cos x + cos(x+π) = 0
         两步并置，即 K1／K2 所论的"同形态"的机器见证。
   本稿范围：四定理
     定理1  prenary_pref_eq            : Pref(δ₀) = 1 − 2/δ₀
     定理2  prenary_pref_zero_iff      : Pref(δ₀) = 0 ⟺ δ₀ = 2
     定理3  prenary_opposite_pair_zero : cos x + cos(x+π) = 0（方向侧）
     定理4  prenary_dir_moment_zero    : 四个对称方向的 cos 之和 = 0
   不做：不主张"偏好量"的定义已成立（§9.3 是候选）；不引入方向分布 μ；
         不主张 K1／K2 的"统一"已被证明（本件只给两个实例的形态一致）。
   注：本件自带所需引理，独立可提交。上承 Day28-14（两档余量与 δ₀ = 2）。
   日期：2026-09-28
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28P

/-- 偏好量（相对尺度）：放大侧余量 − 缩小侧余量，无量纲。
    ⚠️ 必须标 noncomputable：定义体含除法 -/
noncomputable def Pref (δ₀ : ℝ) : ℝ := (1 - 1 / δ₀) - 1 / δ₀

/-- 定理1（偏好量的显式形式）：Pref(δ₀) = 1 − 2/δ₀ -/
theorem prenary_pref_eq (δ₀ : ℝ) (hδ : δ₀ ≠ 0) :
    Pref δ₀ = 1 - 2 / δ₀ := by
  unfold Pref
  field_simp
  ring

/-- 定理2（两档等宽 ⟺ 不动点落在中点）：Pref(δ₀) = 0 ⟺ δ₀ = 2 -/
theorem prenary_pref_zero_iff (δ₀ : ℝ) (hδ : 0 < δ₀) :
    Pref δ₀ = 0 ↔ δ₀ = 2 := by
  have hne : δ₀ ≠ 0 := ne_of_gt hδ
  rw [prenary_pref_eq δ₀ hne]
  constructor
  · intro h
    have h1 : 2 / δ₀ = 1 := by linarith
    have h2 : 2 = δ₀ := by
      rw [div_eq_iff hne] at h1
      linarith
    linarith
  · intro h
    rw [h]
    norm_num

/-- 定理3（方向侧：对径成对 ⟹ 中心量为 0）：cos x + cos(x+π) = 0 -/
theorem prenary_opposite_pair_zero (x : ℝ) :
    Real.cos x + Real.cos (x + Real.pi) = 0 := by
  rw [Real.cos_add_pi]
  ring

/-- 定理4（四个对称方向的 cos 之和 = 0） -/
theorem prenary_dir_moment_zero :
    Real.cos 0 + Real.cos (Real.pi / 2) + Real.cos Real.pi + Real.cos (3 * Real.pi / 2) = 0 := by
  have h2 := prenary_opposite_pair_zero 0
  have h4 := prenary_opposite_pair_zero (Real.pi / 2)
  have h1 : Real.pi = 0 + Real.pi := by ring
  have h3 : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
  rw [h1, h3]
  linarith

end PrenaryDay28P
