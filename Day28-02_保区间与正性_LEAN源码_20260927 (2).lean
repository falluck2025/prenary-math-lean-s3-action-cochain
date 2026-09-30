import Mathlib

/-! ================================================================
   偏元数学 · Day28-02 · 动作上链与和乐 · 保区间与正性
   ------------------------------------------------------------------
   核心：F 把开区间 (0,c) 映回 (0,c)；残差的"有界且不越界"是 A2′ 的实现选择。
   本稿范围：五定理
     定理1  F_complement        : c − F x y c = (c−x)(c−y)/c  （自带，便于独立提交）
     定理2  F_pos               : 0<x,y<c ⟹ 0 < F x y c
     定理3  F_lt                : 0<x,y<c ⟹ F x y c < c
     定理4  eps_ne_zero         : 0<ε ⟹ ε ≠ 0
     定理5  F_preserves_interval: 0<x,y<c ⟹ 0 < F x y c ∧ F x y c < c
   不做：不讨论 F 的选取是否唯一（F 由同胚 h 参数化，属另一件）。
   注：本件自带 F 的定义与补量引理，便于独立提交。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ----------------------------------------------------------------
   ⚠️ 本件未在本地编译过；若报错请贴回。
   ================================================================ -/

namespace PrenaryDay28B

/-- 残差层不变区间上的保区间运算：F(x,y;c) = x + y − x*y/c
    ⚠️ 必须标 noncomputable：`x*y/c` 依赖 `Real.instDivInvMonoid`（noncomputable） -/
noncomputable def F (x y c : ℝ) : ℝ := x + y - x*y/c

/-- 定理1（补量形式）：c − F x y c = (c−x)(c−y)/c -/
theorem F_complement (x y c : ℝ) (hc : c ≠ 0) :
    c - F x y c = (c-x)*(c-y)/c := by
  unfold F
  field_simp
  ring

/-- 定理2（正性）：0<x, 0<y, y<c, 0<c ⟹ 0 < F x y c -/
theorem F_pos (x y c : ℝ) (hx : 0 < x) (hy : 0 < y) (hc : 0 < c) (hyc : y < c) :
    0 < F x y c := by
  have h : F x y c = x * (c - y) / c + y := by
    unfold F
    field_simp
    ring
  rw [h]
  have hcy : 0 < c - y := by linarith
  have h1 : 0 < x * (c - y) / c := by positivity
  linarith

/-- 定理3（保上界）：0<x<c, 0<y<c, 0<c ⟹ F x y c < c
    注：证明只用 hxc / hyc / hc；hx / hy 保留是为了接口与"开区间"表述一致，
        故加 `_` 前缀（不改接口、不触发 unusedVariables warning）。 -/
theorem F_lt (x y c : ℝ) (_hx : 0 < x) (_hy : 0 < y) (hc : 0 < c)
    (hxc : x < c) (hyc : y < c) :
    F x y c < c := by
  have h : c - F x y c = (c-x)*(c-y)/c := F_complement x y c (ne_of_gt hc)
  have hcx : 0 < c - x := by linarith
  have hcy : 0 < c - y := by linarith
  have h2 : 0 < (c-x)*(c-y)/c := by positivity
  linarith

/-- 定理4（推论）：0 < ε ⟹ ε ≠ 0 -/
theorem eps_ne_zero {ε : ℝ} (h : 0 < ε) : ε ≠ 0 := ne_of_gt h

/-- 定理5（保区间）：0<x,y<c ⟹ 0 < F x y c ∧ F x y c < c -/
theorem F_preserves_interval (x y c : ℝ) (hx : 0 < x) (hy : 0 < y) (hc : 0 < c)
    (hxc : x < c) (hyc : y < c) :
    0 < F x y c ∧ F x y c < c :=
  ⟨F_pos x y c hx hy hc hyc, F_lt x y c hx hy hc hxc hyc⟩

end PrenaryDay28B
