import Mathlib

/-! ================================================================
   偏元数学 · Day28-14 · 缩放那一支 · 两档余量与 δ₀ = 2
   ------------------------------------------------------------------
   核心：缩放取值被限制在 (0, δ₀)，以不动点 1 为界，分"缩小"（r<1）与
         "放大"（1<r）两档。本件落定两档的"余量"结构：
         ① δ₀ ≤ 1 时整个区间落在缩小侧（没有"放大"可言）；
         ② 1 < δ₀ 时两档皆非空；
         ③ 两档余量相等 ⟺ δ₀ = 2。
         （"余量"取"I 侧可取长度"：缩小侧 min δ₀ 1，放大侧 max (δ₀−1) 0。）
   本稿范围：三定理
     定理1  prenary_small_side_full : δ₀ ≤ 1 ⟹ (0,δ₀) 全在缩小侧
     定理2  prenary_both_sides      : 1 < δ₀ ⟹ 两档皆非空
     定理3  prenary_margin_balance  : 0<δ₀ ⟹ (min δ₀ 1 = max (δ₀−1) 0 ⟺ δ₀ = 2)
   不做：不主张 δ₀ = 2 在物理上特殊；不主张"量的偏好"已成立；
         "余量"取"侧向可取长度"是一种选择，不是唯一度量。
   注：本件自带所需引理，独立可提交。上承 Day28-11（互逆配对与区间不对称）。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28M

/-- 定理1（δ₀ ≤ 1 时没有"放大"档）：整个 (0,δ₀) 落在缩小侧 -/
theorem prenary_small_side_full (δ₀ r : ℝ) (hrδ : r < δ₀) (hδ : δ₀ ≤ 1) :
    r < 1 := by
  linarith

/-- 定理2（1 < δ₀ 时两档皆非空）：缩小侧与放大侧都取得到值 -/
theorem prenary_both_sides (δ₀ : ℝ) (h : 1 < δ₀) :
    (∃ r : ℝ, 0 < r ∧ r < δ₀ ∧ r < 1) ∧ (∃ r : ℝ, r < δ₀ ∧ 1 < r) := by
  constructor
  · exact ⟨1 / 2, by norm_num, by linarith, by norm_num⟩
  · exact ⟨(1 + δ₀) / 2, by linarith, by linarith⟩

/-- 定理3（两档余量相等 ⟺ δ₀ = 2）：
    缩小侧余量 min δ₀ 1；放大侧余量 max (δ₀−1) 0。 -/
theorem prenary_margin_balance (δ₀ : ℝ) (hδ : 0 < δ₀) :
    min δ₀ 1 = max (δ₀ - 1) 0 ↔ δ₀ = 2 := by
  rw [min_def, max_def]
  constructor
  · intro h
    split_ifs at h <;> linarith
  · intro h
    subst h
    norm_num

end PrenaryDay28M
