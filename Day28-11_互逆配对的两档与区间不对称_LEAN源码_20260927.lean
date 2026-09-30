import Mathlib

/-! ================================================================
   偏元数学 · Day28-11 · 缩放那一支 · 互逆配对的两档 与 区间的不对称
   ------------------------------------------------------------------
   核心：缩放的"两档"（放大/缩小）在代数上是"互逆配对"——
         若 r·s = 1 且 r>0，则 r<1 当且仅当 1<s；
         而把取值限制在 (0, δ₀) 后，倒数把有界区间送到无界区间，
         这正是"量的偏好"候选 A（区间不对称）的算术起点。
   本稿范围：两定理
     定理1  prenary_inv_pair_lt_one : r*s=1 ∧ 0<r ⟹ (r<1 ↔ 1<s)
     定理2  prenary_inv_image_Ioo  : 0<r ∧ r<δ₀ ⟹ 1/δ₀ < 1/r
   ⚠️ 不做：不主张"量的偏好"已成立（候选 A/B/C 并列，未定）。
   注：本件自带所需引理，独立可提交。上承 Day28-09（倒数对合）。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28J

/-- 定理1（互逆配对的两档）：r·s = 1 且 r > 0 时，r<1 与 1<s 等价 -/
theorem prenary_inv_pair_lt_one {r s : ℝ} (h : r * s = 1) (hr : 0 < r) :
    r < 1 ↔ 1 < s := by
  have hs : 0 < s := by nlinarith [h, hr]
  constructor
  · intro h1
    nlinarith [h, hr, hs, h1]
  · intro h1
    nlinarith [h, hr, hs, h1]

/-- 定理2（区间的不对称）：0<r<δ₀ 时，其倒数大于 1/δ₀ ——
    即倒数把有界区间 (0,δ₀) 送到 (1/δ₀, +∞)，两者永不重合。 -/
theorem prenary_inv_image_Ioo (r δ₀ : ℝ) (hr : 0 < r) (hrδ : r < δ₀) :
    1 / δ₀ < 1 / r := by
  have hδ : 0 < δ₀ := by linarith
  have h1 : r * (1 / r) = 1 := by field_simp [ne_of_gt hr]
  have h2 : δ₀ * (1 / δ₀) = 1 := by field_simp [ne_of_gt hδ]
  have h3 : 0 < 1 / r := by positivity
  have h4 : 0 < 1 / δ₀ := by positivity
  nlinarith [h1, h2, h3, h4, hrδ]

end PrenaryDay28J
