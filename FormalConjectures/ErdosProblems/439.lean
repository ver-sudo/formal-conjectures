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
# Erdős Problem 439

*References:*
- [erdosproblems.com/439](https://www.erdosproblems.com/439)
- [KhSz06] Khalfalah, A. and Szemerédi, E., *On the number of monochromatic solutions of
  $x+y=z^2$*. Combin. Probab. Comput. (2006), 213-227.
- [CGS12] Csikvári, P. and Gyarmati, K. and Sárközy, A., *Density and Ramsey type results on
  algebraic equations with restricted solution sets*. Combinatorica (2012), 425-449.
- [GrLi19] Green, Ben and Lindqvist, Sofia, *Monochromatic solutions to $x+y=z^2$*. Canad. J.
  Math. (2019), 579-605.
-/

@[expose] public section

namespace Erdos439

/--
Is it true that, in any finite colouring of the integers, there must be two integers $x\neq y$
of the same colour such that $x+y$ is a square?

The answer is yes. This was conjectured by Erdős, Roth, Sárközy and T. Sós, and proved by
Khalfalah and Szemerédi [KhSz06].

Formalisation notes.
* A finite colouring of the integers is a map $\mathcal{C} \colon \mathbb{N} \to \mathbb{N}$
  with finite range, the convention used elsewhere in this repository.
* $x$ and $y$ are taken to be positive, matching the statement proved in [KhSz06]. Without the
  hypothesis $x \neq y$ the statement is trivially true, see
  `erdos_439.variants.distinctness_trivialises`.
* Only $x$ and $y$ are required to be monochromatic. The integer whose square is $x+y$ is
  unconstrained; requiring it to have the same colour gives a question with the opposite answer,
  see `erdos_439.variants.all_of_x_y_z_monochromatic`.
-/
@[category research solved, AMS 5 11]
theorem erdos_439 :
    answer(True) ↔
    -- for every finite colouring of the integers
    ∀ 𝓒 : ℕ → ℕ, (Set.range 𝓒).Finite →
      -- there are two distinct positive integers
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧
        -- of the same colour
        𝓒 x = 𝓒 y ∧
        -- whose sum is a square
        IsSquare (x + y) := by
  sorry

/--
Erdős also asks the same question for $k$ th powers: in any finite colouring of the integers must
there be two integers $x \neq y$ of the same colour with $x+y$ a $k$ th power?

The answer is again yes. It follows from the theorem of Khalfalah and Szemerédi [KhSz06] applied
to $f(z) = z^k$, see `erdos_439.variants.khalfalah_szemeredi` and
`erdos_439.variants.pow_satisfies_hypotheses`. That theorem produces an integer $z$; one may take
$z$ to be a natural number because $x+y>0$ forces $z^k>0$, so $z>0$ when $k$ is odd, and $z$ may
be replaced by $\lvert z\rvert$ when $k$ is even.

Formalisation note: $k \geq 2$ excludes two degenerate cases. For $k = 1$ the statement is
trivial, since one may take $z = x+y$. For $k = 0$ it is false, since $x + y = 1$ has no solution
with $x$ and $y$ distinct and positive.
-/
@[category research solved, AMS 5 11]
theorem erdos_439.variants.kth_power :
    answer(True) ↔
    ∀ k : ℕ, 2 ≤ k →
      ∀ 𝓒 : ℕ → ℕ, (Set.range 𝓒).Finite →
        ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ 𝓒 x = 𝓒 y ∧ ∃ z : ℕ, x + y = z ^ k := by
  sorry

/--
Khalfalah and Szemerédi [KhSz06] proved the following more general statement, conjectured by
Erdős, Roth, Sárközy and T. Sós: if $f \in \mathbb{Z}[z]$ is a non-constant polynomial such that
$2 \mid f(z)$ for some integer $z$, then in any finite colouring of the integers there are two
distinct integers $x \neq y$ of the same colour with $x + y = f(z)$ for some integer $z$.

The divisibility hypothesis cannot be dropped, see
`erdos_439.variants.odd_values_have_no_monochromatic_pair`.

Formalisation notes.
* $x$ and $y$ range over the positive integers here, as in `erdos_439`, so $f$ must take
  arbitrarily large positive values. The hypothesis $0 < f.leadingCoeff$ supplies this: together
  with $0 < f.natDegree$ it gives $f(z) \to \infty$, and $f(z) \equiv f(z+2) \pmod 2$ then makes
  the even values of $f$ unbounded above. Without it the statement is false, as $f = -z^2$ shows.
* $x \neq y$ is carried over from the original question. It is also what makes the statement
  non-trivial: for $f = 2g^2$, say, one could otherwise always take $x = y = g(z)^2$.
-/
@[category research solved, AMS 5 11]
theorem erdos_439.variants.khalfalah_szemeredi :
    answer(True) ↔
    ∀ f : Polynomial ℤ, 0 < f.natDegree → 0 < f.leadingCoeff → (∃ z : ℤ, 2 ∣ f.eval z) →
      ∀ 𝓒 : ℕ → ℕ, (Set.range 𝓒).Finite →
        ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ 𝓒 x = 𝓒 y ∧
          ∃ z : ℤ, (x : ℤ) + (y : ℤ) = f.eval z := by
  sorry

/--
The hypothesis that $f$ takes at least one even value cannot be dropped: if $f(z)$ is odd for
every integer $z$, then colouring the integers by their parity leaves no monochromatic pair
$x, y$ with $x + y = f(z)$, not even one with $x = y$.
-/
@[category test, AMS 5 11]
theorem erdos_439.variants.odd_values_have_no_monochromatic_pair
    (f : ℤ → ℤ) (hf : ∀ z, ¬ (2 ∣ f z)) :
    ∃ 𝓒 : ℕ → ℕ, (Set.range 𝓒).Finite ∧
      ∀ x y : ℕ, 𝓒 x = 𝓒 y → ∀ z : ℤ, (x : ℤ) + (y : ℤ) ≠ f z := by
  refine ⟨fun n => n % 2, Set.Finite.subset (Set.finite_Iio 2) ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact Nat.mod_lt _ two_pos
  · intro x y hxy z hz
    refine hf z ?_
    have hxy' : x % 2 = y % 2 := hxy
    have hnat : 2 ∣ x + y := by omega
    have hcast : (2 : ℤ) ∣ ((x + y : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hnat
    rw [← hz]
    push_cast at hcast
    exact hcast

/--
Dropping the requirement $x \neq y$ in `erdos_439` makes the statement trivially true: for every
colouring one may take $x = y = 2$, since $2 + 2 = 2^2$.
-/
@[category test, AMS 5 11]
theorem erdos_439.variants.distinctness_trivialises (𝓒 : ℕ → ℕ) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ 𝓒 x = 𝓒 y ∧ IsSquare (x + y) :=
  ⟨2, 2, two_pos, two_pos, rfl, 2, rfl⟩

/--
The polynomial $f(z) = z^k$ satisfies the hypotheses of
`erdos_439.variants.khalfalah_szemeredi` for every $k \geq 1$: it is non-constant, its leading
coefficient is $1$, and $f(0) = 0$ is even.
-/
@[category test, AMS 5 11]
theorem erdos_439.variants.pow_satisfies_hypotheses (k : ℕ) (hk : 1 ≤ k) :
    0 < (Polynomial.X ^ k : Polynomial ℤ).natDegree ∧
      0 < (Polynomial.X ^ k : Polynomial ℤ).leadingCoeff ∧
      ∃ z : ℤ, 2 ∣ (Polynomial.X ^ k : Polynomial ℤ).eval z :=
  ⟨by simp only [Polynomial.natDegree_X_pow]; omega,
    by simp only [Polynomial.leadingCoeff_X_pow]; norm_num,
    0, by simp [zero_pow (by omega : k ≠ 0)]⟩

/--
The closely related question in which $z$ is also required to have the same colour as $x$ and $y$
has the opposite answer. Csikvári, Gyarmati and Sárközy [CGS12] gave a $16$-colouring of
$\mathbb{N}$ with no monochromatic solution to $x+y=z^2$ other than the trivial $x=y=z=2$, and
Green and Lindqvist [GrLi19, Theorem 1.1] showed that $3$ colours already suffice, while every
$2$-colouring has infinitely many monochromatic solutions.
-/
@[category research solved, AMS 5 11]
theorem erdos_439.variants.all_of_x_y_z_monochromatic :
    answer(False) ↔
    ∀ 𝓒 : ℕ → ℕ, (Set.range 𝓒).Finite →
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ ¬ (x = 2 ∧ y = 2 ∧ z = 2) ∧
        𝓒 x = 𝓒 y ∧ 𝓒 y = 𝓒 z ∧ x + y = z ^ 2 := by
  sorry

end Erdos439
