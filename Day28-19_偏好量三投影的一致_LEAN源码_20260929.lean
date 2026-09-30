import Mathlib

/-! ================================================================
   偏元数学 · Day28-19 · 偏好量：三投影在"均匀"下的一致（K1）
   ------------------------------------------------------------------
   缘起：S-006 V1.2（S-006）§9 草稿 V0.2（§9草稿）的 K1
         —— "把 C 一阶矩写出来，看它是否在均匀分布下约化到
            Pref = 1 − 2/δ₀"。
   本件把 §9 的"一个底层定义 ＋ 三个投影"落成**三条可检的等式**：
     定义   Pref        : Pref(δ₀) = 1 − 2/δ₀   （数版 · 几何特值）
     定理1  prenary_pref_offcenter           : Pref = 2·(中点 − 不动点)
     定理2  prenary_pref_measure_projection  : 测度投影（落侧差）= Pref
     定理3  prenary_pref_stat_projection     : 统计投影（一阶矩偏离）= Pref
     定理4  prenary_pref_balanced            : Pref = 0 ⟺ δ₀ = 2（平衡）
   不做：不引入测度论；"均匀"以"⟨u⟩ = 1/2"这一条假设代替
         （离散均匀会带来 1/N 偏差，故本件不假装连续）。
   注：本件自带所需引理，独立可提交。
       上承 Day28-14（两档余量与 δ₀=2）与 Day28-17（偏好量的相对尺度）。
   日期：2026-09-29
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28R

/-- 偏好量的几何特值（数版）：`Pref(δ₀) = 1 − 2/δ₀`。
    ⚠️ 必须标 noncomputable：定义体含 ℝ 的除法 -/
noncomputable def Pref (δ₀ : ℝ) : ℝ := 1 - 2 / δ₀

/-- 定理1（几何读法）：`Pref` 等于"不动点偏离区间中点的 2 倍"。 -/
theorem prenary_pref_offcenter (δ₀ : ℝ) :
    Pref δ₀ = 2 * (1 / 2 - 1 / δ₀) := by
  unfold Pref
  ring

/-- 定理2（测度投影）：在均匀分布下，放大侧测度 `1 − 1/δ₀`、
    缩小侧测度 `1/δ₀`，其**落侧差**等于 `Pref`。 -/
theorem prenary_pref_measure_projection (δ₀ : ℝ) :
    (1 - 1 / δ₀) - 1 / δ₀ = Pref δ₀ := by
  unfold Pref
  ring

/-- 定理3（统计投影）：若分布的均值居中（`⟨u⟩ = 1/2`），
    则"一阶矩偏离不动点的 2 倍"等于 `Pref`。 -/
theorem prenary_pref_stat_projection (δ₀ meanμ : ℝ) (h : meanμ = 1 / 2) :
    2 * (meanμ - 1 / δ₀) = Pref δ₀ := by
  unfold Pref
  rw [h]
  ring

/-- 定理4（平衡点）：`Pref = 0` 当且仅当 `δ₀ = 2`
    （即不动点恰落在区间中点）。 -/
theorem prenary_pref_balanced (δ₀ : ℝ) (h : δ₀ ≠ 0) :
    Pref δ₀ = 0 ↔ δ₀ = 2 := by
  unfold Pref
  rw [sub_eq_zero]
  constructor
  · intro h1
    field_simp at h1
    linarith
  · rintro rfl
    norm_num

end PrenaryDay28R
