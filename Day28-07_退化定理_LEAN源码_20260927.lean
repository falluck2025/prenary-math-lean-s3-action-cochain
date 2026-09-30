import Mathlib

/-! ================================================================
   偏元数学 · Day28-07 · 动作上链与和乐 · 退化定理（回收式 / 降阶式）
   ------------------------------------------------------------------
   核心：退化（ε→0，即步长趋于零）不是"我们的量趋于 0"，而是它的【降阶】——
         和乐 Hol 本身 ∝ 1/ε（发散），但 Hol·ε 收敛到经典量的确定倍数。
         这一步把"经典量"回收出来，也正是"标准数学是 ε→0 的退化"的那座桥。
   本稿范围：四定理
     定理1  hol_mul_eps      : ε·N = L ⟹ Hol(N)·ε = (π/2)·L      （回收式）
     定理2  hol_mul_eps_div  : 再除 δ₀，等式仍成立                 （降阶式）
     定理3  classical_vs_new : 经典分量（与 N 无关）vs 新分量（∝ N）
     定理4  hol_mono         : N < M ⟹ Hol(N) < Hol(M)           （越精确越大）
   不做：不写"Hol → 0"—— 那与 Hol ∝ 1/ε 相反（只对 c 的上边界分量成立）。
   注：定理1 用"ε·N = L"作前提（而非 ε := L/N），从而全部由 ring 关闭。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ----------------------------------------------------------------
   注：本件不用 ∑ 记法，直接写 Finset.sum。
   ================================================================ -/

namespace PrenaryDay28G

/-- 和乐（纯旋转情形）：每步留下 π/2，N 步累积 -/
noncomputable def hol (N : ℕ) : ℝ := (N : ℝ) * (Real.pi / 2)

/-- 定理1（回收式 · 退化）：设 ε·N = L（走一圈的步长×步数＝周长），
    则 Hol·ε 收敛到经典周长的一个确定倍数 —— 经典量被回收。 -/
theorem hol_mul_eps {L eps : ℝ} {N : ℕ} (h : eps * N = L) :
    hol N * eps = (Real.pi / 2) * L := by
  unfold hol
  rw [← h]
  ring

/-- 定理2（降阶式 · 退化）：Hol·ε 再除以 δ₀，仍等于同一个经典量的倍数。
    即：我们的量在退化中降阶（从 1/ε 降到 O(1)），不是消失。 -/
theorem hol_mul_eps_div {L eps δ₀ : ℝ} {N : ℕ} (h : eps * N = L) :
    hol N * eps / δ₀ = (Real.pi / 2) * L / δ₀ := by
  rw [hol_mul_eps h]

/-- 定理3（分量对照）：新分量（每步 π/2 的动作型量）之和 ∝ 步数 N ——
    与经典分量（上边界型，和与 N 无关）形成对照。 -/
theorem classical_vs_new (N : ℕ) :
    (Finset.range N).sum (fun _ => (Real.pi / 2)) = (N : ℝ) * (Real.pi / 2) := by
  rw [Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul]

/-- 定理4（越精确越大）：步数越多（ε 越小），和乐越大 ——
    这是"精度提高、和乐发散"的机器版陈述。 -/
theorem hol_mono {N M : ℕ} (h : N < M) : hol N < hol M := by
  unfold hol
  have h' : (N : ℝ) < (M : ℝ) := by exact_mod_cast h
  nlinarith [Real.pi_pos]

end PrenaryDay28G

/- ----------------------------------------------------------------
   备选（若某条报错）：
   定理1 若 rw [← h] 后 ring 不关：改 unfold hol; rw [← h]; ring_nf
   定理4 若 nlinarith 报错：改
     have h' : (N : ℝ) < (M : ℝ) := by exact_mod_cast h
     have hp : (0:ℝ) < Real.pi / 2 := by positivity
     nlinarith
   ---------------------------------------------------------------- -/
