/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1205

*References:*
- [erdosproblems.com/1205](https://www.erdosproblems.com/1205)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
-/

@[expose] public section

open Filter Finset

namespace Erdos1205

/--
The number of the congruence classes $a_n \pmod n$, for $1 \leq n \leq x$, that $m$ belongs to.
-/
def coverage (a : ℕ → ℕ) (x m : ℕ) : ℕ := #{n ∈ Finset.Icc 1 x | m ≡ a n [MOD n]}

/--
The values $F$ that are achievable at $x$: there are congruence classes $a_n \pmod n$, one for
each $1 \leq n \leq x$, such that every $1 \leq m \leq x$ satisfies at least $F$ of them.
-/
def Admissible (x : ℕ) : Set ℕ :=
  {k | ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 x, k ≤ coverage a x m}

/--
$F(x)$ is maximal such that there exists, for all $n \leq x$, a congruence class
$a_n \pmod n$ such that every $m \leq x$ satisfies at least $F(x)$ of these congruences.

Formalisation note: $n$ and $m$ both range over $1 \leq n, m \leq x$.
-/
noncomputable def F (x : ℕ) : ℕ := sSup (Admissible x)

/--
In an interval of $x$ consecutive integers at most $\lfloor x/n \rfloor + 1$ lie in a fixed
congruence class mod $n$, because $m \mapsto \lfloor m/n \rfloor$ is injective on that class.
-/
@[category API, AMS 11]
theorem card_filter_modEq_le (x n v : ℕ) :
    #{m ∈ Finset.Icc 1 x | m ≡ v [MOD n]} ≤ x / n + 1 := by
  classical
  have key : #{m ∈ Finset.Icc 1 x | m ≡ v [MOD n]} ≤ #(Finset.range (x / n + 1)) := by
    apply Finset.card_le_card_of_injOn (fun m => m / n)
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hm ⊢
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hm.1.2)
    · intro m hm m' hm' h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm hm'
      have e12 : m % n = m' % n := (hm.2).trans (hm'.2).symm
      have e3 : m / n = m' / n := h
      calc m = n * (m / n) + m % n := (Nat.div_add_mod m n).symm
        _ = n * (m' / n) + m' % n := by rw [e3, e12]
        _ = m' := Nat.div_add_mod m' n
  simpa using key

/--
Any achievable value is at most $\sum_{n \leq x} 1/n + 1$, by double counting: the average over
$m \leq x$ of the number of congruences satisfied by $m$ is at most
$x^{-1}\sum_{n \leq x}(x/n + 1)$, and the minimum is at most the average.
-/
@[category API, AMS 11]
theorem admissible_le (x k : ℕ) (hx : 0 < x) (a : ℕ → ℕ)
    (h : ∀ m ∈ Finset.Icc 1 x, k ≤ coverage a x m) :
    (k : ℚ) ≤ harmonic x + 1 := by
  classical
  have h1 : k * x ≤ ∑ m ∈ Finset.Icc 1 x, coverage a x m := by
    calc k * x = ∑ _m ∈ Finset.Icc 1 x, k := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum h
  have h2 : ∑ m ∈ Finset.Icc 1 x, coverage a x m
      = ∑ n ∈ Finset.Icc 1 x, #{m ∈ Finset.Icc 1 x | m ≡ a n [MOD n]} := by
    simp only [coverage, Finset.card_filter]
    exact Finset.sum_comm
  have h3 : ∑ n ∈ Finset.Icc 1 x, #{m ∈ Finset.Icc 1 x | m ≡ a n [MOD n]}
      ≤ ∑ n ∈ Finset.Icc 1 x, (x / n + 1) :=
    Finset.sum_le_sum fun n _ => card_filter_modEq_le x n (a n)
  have h4 : k * x ≤ ∑ n ∈ Finset.Icc 1 x, (x / n + 1) := le_trans h1 (h2 ▸ h3)
  have h5 : ((k * x : ℕ) : ℚ) ≤ ((∑ n ∈ Finset.Icc 1 x, (x / n + 1) : ℕ) : ℚ) :=
    Nat.cast_le.mpr h4
  have h6 : ((∑ n ∈ Finset.Icc 1 x, (x / n + 1) : ℕ) : ℚ) ≤ (x : ℚ) * harmonic x + x := by
    push_cast
    rw [Finset.sum_add_distrib]
    have hle : ∑ n ∈ Finset.Icc 1 x, ((x / n : ℕ) : ℚ) ≤ ∑ n ∈ Finset.Icc 1 x, (x : ℚ) / n :=
      Finset.sum_le_sum fun n _ => Nat.cast_div_le
    have hsum : ∑ n ∈ Finset.Icc 1 x, (x : ℚ) / n = (x : ℚ) * harmonic x := by
      rw [harmonic_eq_sum_Icc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by rw [div_eq_mul_inv]
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    rw [← hsum]
    push_cast
    linarith
  have hx' : (0 : ℚ) < (x : ℚ) := by exact_mod_cast hx
  have h7 : (k : ℚ) * (x : ℚ) ≤ (harmonic x + 1) * (x : ℚ) := by
    calc (k : ℚ) * (x : ℚ) = ((k * x : ℕ) : ℚ) := by push_cast; ring
      _ ≤ ((∑ n ∈ Finset.Icc 1 x, (x / n + 1) : ℕ) : ℚ) := h5
      _ ≤ (x : ℚ) * harmonic x + (x : ℚ) := h6
      _ = (harmonic x + 1) * (x : ℚ) := by ring
  exact le_of_mul_le_mul_right h7 hx'

/-- The supremum defining `F` is attained. -/
@[category API, AMS 11]
theorem F_mem_admissible (x : ℕ) (hx : 0 < x) : F x ∈ Admissible x := by
  classical
  refine Nat.sSup_mem ⟨0, fun _ => 0, fun m _ => Nat.zero_le _⟩ ⟨x, ?_⟩
  rintro k ⟨a, hk⟩
  have h1 : 1 ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨le_refl 1, hx⟩
  calc k ≤ coverage a x 1 := hk 1 h1
    _ ≤ #(Finset.Icc 1 x) := Finset.card_filter_le _ _
    _ = x := by simp

/--
The upper bound $F(x) \leq \log x + O(1)$, obtained by the pigeonhole argument recorded at
[erdosproblems.com/1205](https://www.erdosproblems.com/1205).

Formalisation note: the source states the bound as $F(x) \leq \sum_{n \leq x} 1/n$. Counting the
elements of $\{1, \dots, x\}$ in a class mod $n$ costs a rounding term, which is why the bound
proved here carries an extra $+1$. Both give $\log x + O(1)$.
-/
@[category research solved, AMS 11]
theorem erdos_1205.parts.upper_bound (x : ℕ) (hx : 0 < x) : (F x : ℚ) ≤ harmonic x + 1 := by
  obtain ⟨a, ha⟩ := F_mem_admissible x hx
  exact admissible_le x (F x) hx a ha

/-- The upper bound in the form $F(x) \leq \log x + 2$. -/
@[category research solved, AMS 11]
theorem erdos_1205.parts.upper_bound_log (x : ℕ) (hx : 0 < x) :
    (F x : ℝ) ≤ Real.log x + 2 := by
  have h1 : ((F x : ℚ) : ℝ) ≤ ((harmonic x + 1 : ℚ) : ℝ) := by
    exact_mod_cast erdos_1205.parts.upper_bound x hx
  have h2 : ((harmonic x : ℚ) : ℝ) ≤ 1 + Real.log x := harmonic_le_one_add_log x
  push_cast at h1
  linarith

/--
The lower bound $F(x) \geq \log x - O(\sqrt{\log x \log\log x})$, proved by choosing the
residues $a_n$ at random, applying a Chernoff bound, and repairing the remaining $m$ greedily.
-/
@[category research solved, AMS 11]
theorem erdos_1205.parts.lower_bound :
    ∃ C : ℝ, ∀ᶠ x : ℕ in atTop,
      Real.log x - C * Real.sqrt (Real.log x * Real.log (Real.log x)) ≤ (F x : ℝ) := by
  sorry

/--
Let $F(x)$ be maximal such that there exists, for all $n \leq x$, a congruence class
$a_n \pmod n$ such that every $m \leq x$ satisfies at least $F(x)$ of these congruences.
Estimate $F(x)$.

A problem of Erdős [Er80]. The answer is
$$\log x - O(\sqrt{\log x\log\log x}) \leq F(x) \leq \log x + O(1).$$
-/
@[category research solved, AMS 11]
theorem erdos_1205 :
    (∃ C : ℝ, ∀ x : ℕ, 0 < x → (F x : ℝ) ≤ Real.log x + C) ∧
      (∃ C : ℝ, ∀ᶠ x : ℕ in atTop,
        Real.log x - C * Real.sqrt (Real.log x * Real.log (Real.log x)) ≤ (F x : ℝ)) :=
  ⟨⟨2, erdos_1205.parts.upper_bound_log⟩, erdos_1205.parts.lower_bound⟩

end Erdos1205
