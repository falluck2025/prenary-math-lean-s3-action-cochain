import Mathlib

/-! ================================================================
   偏元数学 · Day28-08 · 动作上链与和乐 · 判据之不足 与 "缩放不改方向"
   ------------------------------------------------------------------
   核心：① 可见性判据只到"残差层不含 0"这一步，而"非零"本身不足以区分
            —— 见证：任意小的非零正实数存在（"可任意小"并非残差独有）；
         ② "有标准上界"不给出正下界 ⟹ 用"有没有上界"区分非标准无穷小是无效的；
         ③ "缩放不改方向"：正实数缩放保持方向（单位化后不变）。
   本稿范围：四定理
     定理1  prenary_small_nonzero : ∀ δ>0, ∃ ε>0, ε<δ ∧ ε≠0
     定理2  bounded_no_pos_lower  : ∀ δ₀>0, ∀ c>0, ∃ ε>0, ε<δ₀ ∧ ε<c
     定理3  scale_normSq          : ‖(↑r)*z‖ = |r| * ‖z‖   （缩放只改模）
     定理4  scale_preserves_unit  : r>0 ⟹ (↑r*z)/‖↑r*z‖ = z/‖z‖  （缩放不改方向）
   不做：不引入非标准模型（全在标准 ℝ／ℂ 内）；不给"手段加倍"的参数化。
   注：本件自带所需引理，独立可提交。上承 Day28-04／-06／-07（动作型 · 非上边界 · 回收）。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28G

/-- 定理1（"非零"不足以区分）：任意小的非零正实数存在 —— 取 δ/2 -/
theorem prenary_small_nonzero (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε ≠ 0 := by
  have h1 : (0 : ℝ) < δ / 2 := by linarith
  have h2 : δ / 2 < δ := by linarith
  exact ⟨δ / 2, h1, h2, ne_of_gt h1⟩

/-- 定理2（"有上界"不给正下界）：0<ε<δ₀ 的开区间内可取任意小的 ε -/
theorem bounded_no_pos_lower (δ₀ c : ℝ) (hδ₀ : 0 < δ₀) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ₀ ∧ ε < c := by
  have hmin : 0 < min c δ₀ := lt_min hc hδ₀
  refine ⟨min c δ₀ / 2, ?_, ?_, ?_⟩
  · linarith
  · linarith [min_le_right c δ₀]
  · linarith [min_le_left c δ₀]

/-- 定理3（缩放只改模，不涉及方向）：‖r·z‖ = |r|·‖z‖ -/
theorem scale_normSq (r : ℝ) (z : ℂ) :
    ‖(r : ℂ) * z‖ = |r| * ‖z‖ := by
  rw [norm_mul, Complex.norm_ofReal]

/-- 定理4（缩放不改方向）：正实数缩放后，单位化向量不变 -/
theorem scale_preserves_unit (r : ℝ) (z : ℂ) (hr : 0 < r) (hz : z ≠ 0) :
    ((r : ℂ) * z) / ‖(r : ℂ) * z‖ = z / ‖z‖ := by
  rw [scale_normSq, abs_of_pos hr]
  field_simp
  rw [mul_comm]

end PrenaryDay28G
