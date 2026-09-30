import Mathlib

/-! ================================================================
   偏元数学 · Day28-20 · 方向侧 κ 与量侧 Pref 的"同型"（K2）
   ------------------------------------------------------------------
   缘起：S-006 V1.2（S-006）§9 草稿 V0.2（§9草稿）的 K2
         —— "在方向上验证 κ = ⟨cos φ⟩ 与 §9.3 的'偏离中点'
            是同一形态"。
   本件把"同型"落成三条结构事实：
     定理1  prenary_cos_pair      : cos φ + cos(φ+π) = 0（对合配对）
     定理2  prenary_kappa_uniform : 四方向（两对对径）⟹ κ = 0（无偏好）
     定理3  prenary_kappa_missing : 缺一角 ⟹ κ = 1/3 ≠ 0（有偏好）
   不做：不引入测度论；"均匀"以"两两配对相消"表达。
   注：本件自带所需引理，独立可提交。
       上承 Day28-17（偏好量的相对尺度与对称性）与 Day28-19（三投影一致）。
   日期：2026-09-29
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28S

/-- 定理1（对合配对）：方向 `φ` 与其对径 `φ+π` 的余弦相消。 -/
theorem prenary_cos_pair (φ : ℝ) :
    Real.cos φ + Real.cos (φ + Real.pi) = 0 := by
  rw [Real.cos_add_pi]
  ring

/-- 定理2（无偏好）：四方向 ＝ 两对对径 ⟹ `κ = 0`。 -/
theorem prenary_kappa_uniform (a b : ℝ) :
    (Real.cos a + Real.cos (a + Real.pi)) + (Real.cos b + Real.cos (b + Real.pi)) = 0 := by
  rw [prenary_cos_pair a, prenary_cos_pair b]
  ring

/-- 定理3（有偏好）：去掉对径的一角（`π/2`、`3π/2` 两方向），
    余下三元平均 `κ = 1/3 ≠ 0`。 -/
theorem prenary_kappa_missing :
    (Real.cos 0 + Real.cos (Real.pi / 2) + Real.cos (3 * Real.pi / 2)) / 3 = 1 / 3 := by
  have h3 : Real.cos (3 * Real.pi / 2) = 0 := by
    have heq : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
    rw [heq, Real.cos_add_pi, Real.cos_pi_div_two]
    ring
  rw [Real.cos_zero, Real.cos_pi_div_two, h3]
  norm_num

end PrenaryDay28S
