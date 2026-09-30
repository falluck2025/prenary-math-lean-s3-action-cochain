import Mathlib

/-! ================================================================
   偏元数学 · Day28-21 · 复缩放的显式刻画（§8.6 待达项 1）
   ------------------------------------------------------------------
   缘起：S-006 V1.2（S-006）§8.6 待达项 1
         —— "复缩放的显式刻画（λ = |λ|·e^{i·arg λ} 的 Lean 化）"。
   本件把"乘一个非零复数"这件动作落成四条事实：
     定理1  prenary_cscale_norm     : 模律  ‖λ z‖ = ‖λ‖·‖z‖
     定理2  prenary_cscale_ne_zero  : 保 ℂ★（非零乘非零仍非零）
     定理3  prenary_cscale_assoc    : 可结合（先 μ 后 λ ＝ 一次 (λ·μ)）
     定理4  prenary_cscale_polar    : 极式分拆（复缩放 ＝ 实缩放 ∘ 旋转）
   ⚠️ 记法：Lean 里 `λ` 是 `fun` 的关键字、不能作形参名，
      故代码中缩放因子写作 `w`、第二因子写作 `v`（抬头里仍用数学记法 λ、μ）。
   不做：不做 §10 的一般和乐（已另件）；不主张本件即"复缩放"的完整理论。
   注：本件自带所需引理，独立可提交。
       上承 Day28 的第 8、9、10 件（缩放三件）与 §7-8 成文稿（V0.2）。
   日期：2026-09-29
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28T

/-- 复缩放：乘一个非零复数（`w` 为缩放因子、`z` 为被作用的对象）。 -/
def cscale (w z : ℂ) : ℂ := w * z

/-- 定理1（模律）：复缩放的模 ＝ 两模之积。 -/
theorem prenary_cscale_norm (w z : ℂ) : ‖cscale w z‖ = ‖w‖ * ‖z‖ := by
  simp [cscale]

/-- 定理2（保 ℂ★）：非零乘非零仍非零 —— 复缩放把 `ℂ★` 映入 `ℂ★`。 -/
theorem prenary_cscale_ne_zero (w z : ℂ) (hw : w ≠ 0) (hz : z ≠ 0) :
    cscale w z ≠ 0 := by
  simp only [cscale]
  exact mul_ne_zero hw hz

/-- 定理3（可结合）：先做 `v` 再做 `w` ＝ 一次做 `w·v` —— 复缩放是乘法群的作用。 -/
theorem prenary_cscale_assoc (w v z : ℂ) :
    cscale w (cscale v z) = cscale (w * v) z := by
  simp only [cscale]
  ring

/-- 定理4（极式分拆）：把缩放因子写成极式 `w = (r:ℂ)·e^{iθ}`，
    则复缩放 ＝ 实缩放（乘 `r`）∘ 旋转（乘 `e^{iθ}`）。 -/
theorem prenary_cscale_polar (r θ : ℝ) (z : ℂ) :
    cscale ((r : ℂ) * Complex.exp (θ * I)) z
      = (r : ℂ) * (Complex.exp (θ * I) * z) := by
  simp only [cscale]
  ring

-- 说明（不进定理体）：要把定理4的极式与 ‖w‖／arg w 接上，
-- 用一座 Mathlib 桥引理（名待核），形如
--   (‖w‖ : ℂ) * Complex.exp (Complex.arg w * I) = w。
-- 本件暂不依赖它，以保证独立可提交。

end PrenaryDay28T
