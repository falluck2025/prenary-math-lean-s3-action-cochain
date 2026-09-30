import Mathlib

/-! ================================================================
   偏元数学 · Day28-04 · 动作上链与和乐 · 动作型 vs 拓扑型（承重件）
   ------------------------------------------------------------------
   核心：同一条闭路上，两个"沿路求和"的量行为完全不同 ——
         位置标架角的和  Σ Δψ  = 2π        （与步数 N 无关，拓扑型）
         动作偏差的和    Σ δ   = N · (π/2) （正比于 N，      动作型）
         这是"动作型不变量"在机器上的判别：看它是否 ∝ 步数。
   本稿范围：四定理
     定理1   psi_step        : ψ_N(i+1) − ψ_N(i) = 2π/N
     定理2   sum_psi         : Σ Δψ = 2π          （与 N 无关）
     定理3   sum_delta       : Σ δ  = N · (π/2)   （∝ N）
     定理4   contrast        : N=4 与 N=8 的 Σδ 不相等（而 ΣΔψ 相同）
   不做：不写 π₁(ℂ★) = ℤ —— Mathlib 无 fundamentalGroup 现成件；
         改用实值 ΣΔψ = 2π 表达"绕数"，从而把"拓扑 vs 动作"降为两个有限和的比较。
   注：δ = π/2 由"纯旋转 + K0 约束"给出（→ Day28-05）。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ----------------------------------------------------------------
   ⚠️ 记法：本件【不用 ∑ 记法】，直接写 Finset.sum。
   ⚠️ 三稿改动（据二稿报错）：
      ① psi_step 的 ring 改 ring_nf（ring 处理不了 ↑(1+i)）；
      ② sum_delta 用一条 simp 收口（避免"多一步"触发 No goals to be solved）；
      ③ sum_psi 末尾改 field_simp <;> ring（<;> 对零子目标安全）。
   ================================================================ -/

namespace PrenaryDay28D

/-- 位置标架角的"走一圈"模型：ψ_N(i) = (2π / N) · i
    取此写法（先除后乘）是为了让相邻差为常数 2π/N，避免除法出现在求和里。 -/
noncomputable def psi (N : ℕ) (i : ℕ) : ℝ := (2 * Real.pi / N) * i

/-- 动作偏差：纯旋转情形下恒为 π/2（由 K0 约束给出） -/
noncomputable def delta : ℝ := Real.pi / 2

/-- 定理1（相邻差为常数）：ψ_N(i+1) − ψ_N(i) = 2π/N -/
theorem psi_step (N i : ℕ) : psi N (i+1) - psi N i = 2 * Real.pi / N := by
  unfold psi
  push_cast
  ring

/-- 定理2（拓扑型）：Σ Δψ = 2π，与步数 N 无关 -/
theorem sum_psi (N : ℕ) (hN : N ≠ 0) :
    (Finset.range N).sum (fun i => psi N (i+1) - psi N i) = 2 * Real.pi := by
  have h : ∀ i, psi N (i+1) - psi N i = 2 * Real.pi / N := fun i => psi_step N i
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  field_simp <;> ring

/-- 定理3（动作型）：Σ δ = N · (π/2)，正比于步数 -/
theorem sum_delta (N : ℕ) :
    (Finset.range N).sum (fun _ => delta) = (N : ℝ) * (Real.pi / 2) := by
  simp [Finset.sum_const, Finset.card_range, delta]

/-- 定理4（对照）：N=4 与 N=8 的动作量和不相等（而 §定理2 已证位置角和恒为 2π） -/
theorem contrast :
    (Finset.range 4).sum (fun _ => delta) ≠ (Finset.range 8).sum (fun _ => delta) := by
  rw [sum_delta, sum_delta]
  push_cast
  intro h
  linarith [Real.pi_pos]

end PrenaryDay28D

/- ----------------------------------------------------------------
   若某条仍报错，备选：

   psi_step ：
     unfold psi; ring_nf                    （Lean 建议的写法）
     unfold psi; simp only [Nat.cast_add, Nat.cast_one]; ring

   sum_psi 末尾：
     field_simp                             （若它自己就关掉目标）
     have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
     rw [mul_comm] ; rw [mul_div_cancel₀ _ hN']

   sum_delta ：
     rw [Finset.sum_const, Finset.card_range] ; simp only [nsmul_eq_mul] ; rfl

   contrast ：
     若 push_cast 报错，改 norm_num 处理 (4:ℝ) / (8:ℝ) 的 cast。
   ---------------------------------------------------------------- -/
