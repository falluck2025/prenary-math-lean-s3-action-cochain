import Mathlib

/-! ================================================================
   偏元数学 · Day28-09 · 缩放那一支 · 倒数对合与"两档"
   ------------------------------------------------------------------
   核心：缩放的"比例"与"二选一"是同一件事的两面 ——
         比例是 r ∈ ℝ_{>0}；二选一是 r 与 1/r 的两侧，而 r ↦ 1/r 是一个【对合】，
         唯一不动点是 r = 1（"不缩放"）。
   本稿范围：四定理（只落"对合与两档"这一层机器事实）
     定理1  prenary_inv_involutive      : 1/(1/r) = r            （对合）
     定理2  prenary_inv_fixed_iff_one   : 0<r ⟹ (1/r = r ↔ r = 1)（唯一不动点）
     定理3  prenary_trichotomy          : r<1 ∨ r=1 ∨ 1<r        （两档＋分界）
     定理4  prenary_inv_lt_one_of_one_lt: 1<r ⟹ 1/r < 1          （两侧互换）
   ⚠️ 不做：**不主张"它构成一个二态"** —— 二态的成立与否属推演，不在本件范围；
         本件只给"对合 ＋ 两档划分"的机器事实。
   注：本件自带所需引理，独立可提交。上承 Day28-08（缩放不改方向）。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28H

/-- 定理1（倒数对合）：两次取倒数回到自身 -/
theorem prenary_inv_involutive (r : ℝ) : 1 / (1 / r) = r := by
  simp [one_div]

/-- 定理2（唯一不动点）：正实数下，1/r = r 当且仅当 r = 1 -/
theorem prenary_inv_fixed_iff_one (r : ℝ) (hr : 0 < r) : 1 / r = r ↔ r = 1 := by
  rw [div_eq_iff (ne_of_gt hr)]
  constructor
  · intro h
    have h2 : (r - 1) * (r + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h2 with h3 | h4
    · linarith
    · linarith
  · intro h
    rw [h]
    ring

/-- 定理3（两档＋分界）：小于、等于、大于 1 -/
theorem prenary_trichotomy (r : ℝ) : r < 1 ∨ r = 1 ∨ 1 < r := by
  rcases lt_trichotomy r 1 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- 定理4（两侧互换）：r>1 时其倒数落在"缩小"一侧 -/
theorem prenary_inv_lt_one_of_one_lt (r : ℝ) (hr : 1 < r) : 1 / r < 1 := by
  have h0 : (0 : ℝ) < r := by linarith
  rw [div_lt_iff h0]
  nlinarith

end PrenaryDay28H
