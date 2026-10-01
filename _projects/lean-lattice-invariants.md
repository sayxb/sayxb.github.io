---
layout: page
title: Lattices from their Invariants in Lean
description: Walking through a Lean 4 formalisation of the theorem that a complex lattice is determined by its invariants $g_2$ and $g_3$, via the Laurent expansion of the Weierstrass $\wp$-function.
importance: 1
category: Lean
related_publications: false
---

In June I took part in part 1 of the [Lean-LMFDB](https://multramate.github.io/lean-lmfdb/) workshop, working with Prof. John Cremona. One of the things we formalised was the classical fact that a lattice in $$\mathbb{C}$$ is determined by its invariants $$g_2$$ and $$g_3$$. This page is a breakdown of that Lean file, block by block. For each block I go through the maths, the Lean syntax, and why the proof actually goes through. Writing out why each tactic call works is the best way I know of checking that I understand a proof, so this is really as much for me as for anyone else.

## Problem statement

A lattice is $$L = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2 \subset \mathbb{C}$$, where $$\omega_1, \omega_2$$ are linearly independent over $$\mathbb{R}$$. Its Eisenstein series and invariants are

$$
G_k(L) = \sum_{l \in L \setminus \{0\}} \frac{1}{l^k}, \qquad g_2(L) = 60\,G_4(L), \qquad g_3(L) = 140\,G_6(L),
$$

and its Weierstrass function is

$$
\wp_L(z) = \frac{1}{z^2} + \sum_{l \in L \setminus \{0\}} \left( \frac{1}{(z-l)^2} - \frac{1}{l^2} \right).
$$

**Theorem.** If $$g_2(L_1) = g_2(L_2)$$ and $$g_3(L_1) = g_3(L_2)$$, then $$L_1 = L_2$$.

Scaling $$L \mapsto \lambda L$$ sends $$g_2 \mapsto \lambda^{-4} g_2$$ and $$g_3 \mapsto \lambda^{-6} g_3$$, so if both are required to match then you pin down the lattice itself. $$\lambda^4, \lambda^6 = 1$$ implies that $$\lambda$$ is both a 4th and 6th root of unity, which gives that $$/lambda$$ is $1,-1$, so $$L \mapsto \pm L$$. The set of points of $$-L$$ is the same as $$L$$ though so regardless of what you take $$\lambda$$ to be you get the same set of points.

## The idea of the proof

Roughly, each term of the power series of Weierstrass $\wp$ equation for a period lattice $$L$$ gives a pole that determines a point in the lattice. You can show that the poles and the value of $$\wp$$ for a lattice near the poles are determined by $$g_2$$ and $$g_3$$, and so two lattices with the same $$g_2$$ and $$g_3$$ invariants have the same points. Proof was constructed in these steps:

Much of the proof, with a lot of direction, was written by Claude's Opus and Fable 5. They were pretty good at writing Lean code that at least compiles, though they struggled with the logic of the proof. I think though by now, something like this could probably be one-shot by Opus 5.5 without much direction.

1. Near $$0$$ we can write $$\wp_L(z) = 1/z^2 + f_L(z)$$ with $$f_L$$ analytic, and the Taylor coefficients of $$f_L$$ are Eisenstein series, $$f_L^{(n)}(0) = (n+1)!\,G_{n+2}(L)$$.
2. The differential equation $$(\wp')^2 = 4\wp^3 - g_2\wp - g_3$$ turns into a recursion for these Taylor coefficients.
3. The recursion says every coefficient is determined by $$G_4$$ and $$G_6$$, i.e. by $$g_2$$ and $$g_3$$. So $$\wp_{L_1} = \wp_{L_2}$$ near $$0$$.
4. By the identity theorem, $$\wp_{L_1} = \wp_{L_2}$$ everywhere away from both lattices.
5. The poles of $$\wp_L$$ are exactly the points of $$L$$, so $$L_1 = L_2$$.

A lot of the heavy lifting is already in Mathlib, in Andrew Yang's file `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`. It has the definitions of $$\wp$$, $$\wp'$$, $$G_k$$, $$g_2$$ and $$g_3$$, the differential equation, the order of the poles, and a closed formula for the Taylor coefficients. Our job was mostly to put these together, which turned out to be a fair amount of work in itself.

### A word on junk values

Lean has no partial functions, so division by zero has to return something, and it returns $$0$$. Mathlib defines $$\wp_L$$ as a sum over the whole lattice, $$\sum_{l \in L} \big(1/(z-l)^2 - 1/l^2\big)$$, where the $$l = 0$$ term is $$1/z^2 - 1/0 = 1/z^2$$ (the pole term). At $$z = 0$$ every term vanishes, so $$\wp_L(0) = 0$$, and then $$\wp_L$$ vanishes at every lattice point by periodicity. This sounds a bit like cheating, but it's convenient: several identities below hold for every $$z \in \mathbb{C}$$, not just away from the lattice, so we can use them without dragging hypotheses around.

## 1. Imports and setup

```
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Topology.Algebra.Module.Cardinality

open Filter Topology
open scoped Nat

namespace PeriodPair

noncomputable section

attribute [local fun_prop] AnalyticAt.contDiffAt

variable (L : PeriodPair)
```

**The maths.** A `PeriodPair` is a structure with exactly three fields: two complex numbers `ω₁`, `ω₂` and a proof `indep` that they are $$\mathbb{R}$$-linearly independent. Everything else is a *definition* in the `PeriodPair` namespace rather than a field: `L.lattice` (the $$\mathbb{Z}$$-span of the periods, as a `Submodule ℤ ℂ`), `L.G n`, `L.g₂`, `L.g₃` and `℘[L]`. So `variable (L : PeriodPair)` fixes a pair of periods, and all of those become available through dot notation.

**The Lean.** Apart from the Weierstrass file, the other two imports are quite specific. `Mathlib.Data.Nat.Choose.Cast` gives `Nat.cast_choose_two`, which says $$\binom{n}{2} = n(n-1)/2$$ once cast into a field (used in section 6). `Mathlib.Topology.Algebra.Module.Cardinality` gives `Set.Countable.dense_compl`, which says a countable subset of a (nontrivial) vector space over a complete field has dense complement (used in section 10).

`open Filter Topology` brings in the filter notation that the whole proof is written in. `𝓝 a` is the filter of neighbourhoods of `a`, and `𝓝[≠] a` is the punctured version. `∀ᶠ z in F, P z` reads "`P` holds eventually along `F`", i.e. on some set belonging to `F`, so `∀ᶠ z in 𝓝 0, P z` just means "`P` holds on a neighbourhood of `0`". Similarly `f =ᶠ[F] g` means `f` and `g` agree eventually along `F`, i.e. they have the same germ. `open scoped Nat` gives the factorial notation `n !`.

Working inside `namespace PeriodPair` does two things. Our lemmas get the prefix `PeriodPair.`, which is what lets us write `L.eventually_notMem_lattice` later. It also makes the notations `℘[L]`, `℘[L - l₀]` and `℘'[L]` available, since Mathlib declares them as scoped to this namespace.

`noncomputable section` is harmless but not needed, as the file contains no definitions. The line `attribute [local fun_prop] AnalyticAt.contDiffAt` teaches the `fun_prop` tactic that analytic functions are smooth (`ContDiffAt`). The Leibniz rule lemmas we use want `ContDiffAt` hypotheses, while Mathlib hands us analyticity, so this bridges the two. It's `local`, so it only applies to this file, and Mathlib does exactly the same thing in the Weierstrass file.

## 2. The Laurent expansion of ℘ at 0

```
/-- Points of a punctured neighbourhood of `0` are not lattice points. -/
lemma eventually_notMem_lattice : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds (L.compl_lattice_diff_singleton_mem_nhds 0),
    self_mem_nhdsWithin] with z hz (hz0 : z ≠ 0) hzL
  exact hz ⟨hzL, hz0⟩

/-- The pole part of `℘` at `0`: `℘[L] z = ℘[L - 0] z + 1/z²` (globally, thanks to
junk values: at `z = 0` both sides are `0`). -/
lemma weierstrassP_eq (z : ℂ) : ℘[L] z = ℘[L - (0 : ℂ)] z + 1 / z ^ 2 := by
  rw [← L.weierstrassPExcept_add 0 z]
  simp

/-- The pole part of `℘'` at `0`, globally. -/
lemma derivWeierstrassPExcept_zero_eq (z : ℂ) :
    ℘'[L - (0 : ℂ)] z = ℘'[L] z + 2 / z ^ 3 := by
  simpa using L.derivWeierstrassPExcept_def 0 z

/-- The Taylor coefficients of `℘[L - 0]` at `0` are the Eisenstein series `G`. -/
lemma iteratedDeriv_weierstrassPExcept_zero (n : ℕ) :
    iteratedDeriv n ℘[L - (0 : ℂ)] 0 =
      if n = 0 then 0 else ((n + 1)! : ℂ) * L.G (n + 2) := by
  rw [L.iteratedDeriv_weierstrassPExcept_self 0]
  simp
```

**The maths.** Mathlib's `℘[L - l₀]` is the $$\wp$$-sum with the $$l_0$$ term removed. Taking $$l_0 = 0$$ removes exactly the pole at the origin, so

$$
f(z) := \wp_{L}(z) - \frac{1}{z^2} = \sum_{l \in L \setminus\{0\}} \left( \frac{1}{(z-l)^2} - \frac{1}{l^2} \right)
$$

is analytic near $$0$$, with $$f(0) = 0$$. Throughout, $$f$$ is `℘[L - 0]`. Differentiating each term $$n$$ times gives $$\frac{d^n}{dz^n}(z-l)^{-2} = (-1)^n (n+1)!\,(z-l)^{-(n+2)}$$, and at $$z = 0$$ the signs cancel, so

\begin{equation}
f^{(n)}(0) = (n+1)!\; G_{n+2}(L) \qquad (n \geq 1).
\end{equation}

For odd $$k$$ we have $$G_k = 0$$, since the terms for $$l$$ and $$-l$$ cancel, so all the odd coefficients vanish and $$f$$ is even. In particular $$f'(0) = 2!\,G_3 = 0$$.

The same story happens for $$\wp'$$. Mathlib's `℘'[L - l₀]` is the series $$\sum_{l \neq l_0} -2/(z-l)^3$$, defined as its own series rather than as a derivative, and removing the $$l = 0$$ term gives $$\wp'_L(z) = -2/z^3 + (\text{analytic})$$.

**The Lean.** `eventually_notMem_lattice` says that close to $$0$$, but not at $$0$$, there are no lattice points. This is just discreteness: Mathlib's `compl_lattice_diff_singleton_mem_nhds 0` says $$(L \setminus \{0\})^c$$ is a neighbourhood of $$0$$. The tactic `filter_upwards [h₁, …, hₖ] with z a₁ … aₖ` turns a goal `∀ᶠ z in F, P z` into the goal `P z`, where `a₁, …, aₖ` are the properties from `h₁, …, hₖ` at the point `z`. Here:

- `mem_nhdsWithin_of_mem_nhds` weakens "neighbourhood of 0" to "punctured neighbourhood of 0", and gives `hz : z ∉ L \ {0}`.
- `self_mem_nhdsWithin` gives `z ∈ {0}ᶜ`. Since `𝓝[≠] 0` is literally `𝓝[{0}ᶜ] 0`, this unfolds to `z ≠ 0`, which is why the type ascription `(hz0 : z ≠ 0)` is accepted.
- The goal `z ∉ L.lattice` is by definition `z ∈ L.lattice → False`, so the extra name `hzL` introduces the assumption `z ∈ L.lattice`.

Then `hz` says `¬(z ∈ L ∧ z ≠ 0)`, and feeding it `⟨hzL, hz0⟩` gives `False`.

For `weierstrassP_eq`, Mathlib's `weierstrassPExcept_add` says `℘[L - l₀] z + (1/(z - l₀)² - 1/l₀²) = ℘[L] z` for a lattice point `l₀`. The `0` we pass is `(0 : L.lattice)`, since the lemma wants a lattice element. Rewriting right to left replaces `℘[L] z` in the goal, and `simp` tidies up the coercion `↑0`, the `z - 0` and the junk value `1/0² = 0`. `derivWeierstrassPExcept_zero_eq` is the same thing for `℘'`, using `simpa`, which simplifies the given lemma and the goal and then matches them.

For the Taylor coefficients, Mathlib's `iteratedDeriv_weierstrassPExcept_self` gives, at the excluded point `l`, that the $$n$$-th derivative is `if n = 0 then ℘[L - l] l else (n + 1)! * L.sumInvPow l (n + 2)`, where `sumInvPow x r` is $$\sum_{l} (l-x)^{-r}$$. At $$l = 0$$, `simp` uses `weierstrassPExcept_zero` (the value at $$0$$ is $$0$$) and `sumInvPow_zero` (`sumInvPow 0` is `G`). Both sums technically include the $$l = 0$$ term, but that term is $$0^{-r} = 0$$ by junk values, so nothing goes wrong.

**Why it works.** All four lemmas are repackagings of facts Mathlib already proves. The point is to get them into the exact shape needed later, centred at $$0$$ with the pole written out.

## 3. ℘′ doesn't vanish near 0

```
/-- `℘'` does not vanish in a punctured neighbourhood of `0` (it blows up like `-2/z³`). -/
lemma eventually_derivWeierstrassP_ne_zero :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), ℘'[L] z ≠ 0 := by
  have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), ℘'[L - (0 : ℂ)] z ∈ Metric.ball (0 : ℂ) 1 := by
    apply (L.analyticAt_derivWeierstrassPExcept 0).continuousAt.eventually_mem
    rw [L.derivWeierstrassPExcept_zero_zero]
    exact Metric.ball_mem_nhds _ one_pos
  have h2 : ∀ᶠ z : ℂ in 𝓝 0, z ∈ Metric.ball (0 : ℂ) 1 := Metric.ball_mem_nhds _ one_pos
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds, h2.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz1 hz2 (hz0 : z ≠ 0) hzero
  rw [mem_ball_zero_iff] at hz1 hz2
  rw [L.derivWeierstrassPExcept_zero_eq, hzero, zero_add, norm_div, norm_pow] at hz1
  have hz : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have h2' : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2', div_lt_one (by positivity)] at hz1
  have h3 : ‖z‖ ^ 3 < 1 := pow_lt_one₀ (norm_nonneg z) hz2 (by norm_num)
  linarith
```

**The maths.** Later (section 4) we need to divide by $$\wp'$$, so we need it to be nonzero near $$0$$. Write $$\wp'_L(z) = -2/z^3 + g(z)$$, where $$g$$ is `℘'[L - 0]`. This $$g$$ is analytic at $$0$$ and $$g(0) = 0$$, since $$g$$ is odd. If $$\wp'_L(z) = 0$$ then $$g(z) = 2/z^3$$. But for $$z$$ close to $$0$$ we have $$\lvert g(z) \rvert < 1$$, while for $$\lvert z \rvert < 1$$ we have $$\lvert 2/z^3 \rvert > 2$$. So the pole term wins, and $$\wp'$$ can't vanish.

**The Lean.** `h1` says $$\lvert g(z) \rvert < 1$$ near $$0$$. It uses continuity of $$g$$ at $$0$$ (`ContinuousAt.eventually_mem`: if $$g(0)$$ lies in an open set then so does $$g(z)$$ for $$z$$ near $$0$$), together with $$g(0) = 0$$ from `derivWeierstrassPExcept_zero_zero`. `h2` says $$\lvert z \rvert < 1$$ near $$0$$. Both are statements on the full neighbourhood `𝓝 0`, so `filter_mono nhdsWithin_le_nhds` moves them to the punctured neighbourhood. This uses the fact that `𝓝[≠] 0 ≤ 𝓝 0`: anything true near $$0$$ is true near $$0$$ away from $$0$$.

As before, the goal `℘'[L] z ≠ 0` means `℘'[L] z = 0 → False`, so the last name `hzero` introduces `℘'[L] z = 0`, and we're aiming for a contradiction. The rewrites turn `hz1 : ‖℘'[L - 0] z‖ < 1` into `‖2‖ / ‖z‖ ^ 3 < 1`, then `div_lt_one` turns that into `2 < ‖z‖ ^ 3`. `hz` is proved first so that `positivity` can check `0 < ‖z‖ ^ 3`, which `div_lt_one` needs. `pow_lt_one₀` turns `‖z‖ < 1` into `‖z‖ ^ 3 < 1`, and `linarith` spots that $$2 < \lVert z \rVert^3 < 1$$ is impossible.

**Why it works.** It's the standard "the pole dominates" argument, written out with explicit norm bounds. It's correct, but quite long for what it does; I come back to this at the end.

## 4. The second-order differential equation

```
/-- The second-derivative differential equation, in a punctured neighbourhood of `0`. -/
lemma eventually_deriv_derivWeierstrassP :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  filter_upwards [L.eventually_notMem_lattice, L.eventually_derivWeierstrassP_ne_zero]
    with z hz hz'
  have hev : (fun w ↦ ℘'[L] w ^ 2) =ᶠ[𝓝 z]
      fun w ↦ 4 * ℘[L] w ^ 3 - L.g₂ * ℘[L] w - L.g₃ := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact L.derivWeierstrassP_sq w hw
  have hd' : DifferentiableAt ℂ ℘'[L] z :=
    (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt
  have hd : DifferentiableAt ℂ ℘[L] z :=
    (L.analyticOnNhd_weierstrassP z hz).differentiableAt
  have hP : HasDerivAt ℘[L] (℘'[L] z) z := by
    simpa using hd.hasDerivAt
  have h1 := hd'.hasDerivAt.fun_pow 2
  have h2 := (((hP.fun_pow 3).const_mul (4 : ℂ)).fun_sub (hP.const_mul L.g₂)).sub_const L.g₃
  apply mul_left_cancel₀ (a := 2 * ℘'[L] z) (by simpa using hz')
  have hder := hev.deriv_eq
  rw [h1.deriv, h2.deriv] at hder
  push_cast at hder
  linear_combination hder
```

**The maths.** Differentiating $$(\wp')^2 = 4\wp^3 - g_2\wp - g_3$$ gives

\begin{equation}
2\wp'\wp'' = 12\wp^2\wp' - g_2\wp',
\end{equation}

and wherever $$\wp' \neq 0$$ we can divide by $$2\wp'$$ to get

\begin{equation}
\wp'' = 6\wp^2 - \frac{g_2}{2}.
\end{equation}

By sections 2 and 3, near $$0$$ (but not at $$0$$) we're away from the lattice and $$\wp' \neq 0$$, so this holds on a punctured neighbourhood of $$0$$.

**The Lean.** There's one subtle point here. You can't differentiate an identity that only holds at a single point: to conclude that two functions have the same derivative at $$z$$, they have to agree on a whole neighbourhood of $$z$$. That's what `hev` provides. The differential equation (`derivWeierstrassP_sq`) holds off the lattice, the complement of the lattice is open (`isClosed_lattice.isOpen_compl`), and it contains $$z$$, so it's a neighbourhood of $$z$$. Then `Filter.EventuallyEq.deriv_eq` says functions with the same germ at $$z$$ have the same derivative there, which gives `hder`.

`AnalyticOnNhd ℂ f s` means `∀ x ∈ s, AnalyticAt ℂ f x`, so `analyticOnNhd_derivWeierstrassP z hz` is analyticity at `z`, and `.differentiableAt` weakens that. `hP` says the derivative of $$\wp$$ is $$\wp'$$. It comes from `simpa`, which uses Mathlib's simp lemma `deriv_weierstrassP : deriv ℘[L] = ℘'[L]`; this holds globally, again thanks to junk values.

`h1` and `h2` compute derivatives of the two sides of the differential equation. `HasDerivAt.fun_pow` is the power rule ($$\frac{d}{dz} f^n = n f^{n-1} f'$$), and `h2` builds up the right-hand side one operation at a time: `fun_pow 3`, then `const_mul 4`, then subtract `const_mul g₂`, then `sub_const g₃`.

To divide by $$2\wp'$$, `apply mul_left_cancel₀ (a := 2 * ℘'[L] z) _` changes the goal $$b = c$$ into $$a b = a c$$; this is valid since $$a \neq 0$$, and `(by simpa using hz')` provides that. `push_cast` tidies up casts and exponents like `2 - 1`. Finally, `linear_combination hder` closes a goal `a = b` given `hder : c = d` by checking that $$(a - b) - (c - d) = 0$$ is a ring identity, which it is here.

**Why it works.** The cancellation is valid exactly because we restricted to points where $$\wp' \neq 0$$. This is the only reason section 3 exists.

## 5. The key identity for the pole-free part

```
/-- The pole-cleared second-derivative equation, as a germ at `0`:
`z² ℘''(z) = 6 z² f(z)² + 12 f(z) - (g₂/2) z²` where `f = ℘[L - 0]`. -/
lemma key_eventuallyEq :
    (fun z : ℂ ↦ z ^ 2 * deriv ℘'[L - (0 : ℂ)] z) =ᶠ[𝓝 (0 : ℂ)]
      fun z ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))
        + 12 * ℘[L - (0 : ℂ)] z - L.g₂ / 2 * z ^ 2 := by
  have h1 : (fun z : ℂ ↦ z ^ 2 * deriv ℘'[L - (0 : ℂ)] z) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun z ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))
        + 12 * ℘[L - (0 : ℂ)] z - L.g₂ / 2 * z ^ 2 := by
    filter_upwards [L.eventually_notMem_lattice, self_mem_nhdsWithin,
      L.eventually_deriv_derivWeierstrassP] with z hzL (hz0 : z ≠ 0) hD
    have hEq : ℘'[L - (0 : ℂ)] = fun w ↦ ℘'[L] w + 2 / w ^ 3 :=
      funext L.derivWeierstrassPExcept_zero_eq
    have hden : HasDerivAt (fun w : ℂ ↦ w ^ 3) (3 * z ^ 2) z := by
      simpa using hasDerivAt_pow 3 z
    have hz3 : HasDerivAt (fun w : ℂ ↦ 2 / w ^ 3) (-6 / z ^ 4) z := by
      have h := (hasDerivAt_const z (2 : ℂ)).div hden (pow_ne_zero 3 hz0)
      convert h using 1
      field_simp
      ring
    have hd' : DifferentiableAt ℂ ℘'[L] z :=
      (L.analyticOnNhd_derivWeierstrassP z hzL).differentiableAt
    have hsum : HasDerivAt (fun w ↦ ℘'[L] w + 2 / w ^ 3)
        (deriv ℘'[L] z + -6 / z ^ 4) z := hd'.hasDerivAt.add hz3
    rw [hEq, hsum.deriv, hD, L.weierstrassP_eq z]
    field_simp
    ring
  have h2 : (fun z : ℂ ↦ z ^ 2 * deriv ℘'[L - (0 : ℂ)] z) =ᶠ[pure (0 : ℂ)]
      (fun z ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))
        + 12 * ℘[L - (0 : ℂ)] z - L.g₂ / 2 * z ^ 2) :=
    Filter.eventually_pure.mpr (by simp)
  have h12 := Filter.eventually_sup.mpr ⟨h1, h2⟩
  rwa [nhdsNE_sup_pure] at h12
```

**The maths.** Now substitute the Laurent expansion into $$\wp'' = 6\wp^2 - g_2/2$$. From section 2, $$\wp = f + z^{-2}$$ and `℘'[L - 0]` $$= \wp' + 2z^{-3}$$, so differentiating gives

$$
\frac{d}{dz}\,\wp'_{L\setminus 0} = \wp'' - \frac{6}{z^4} = 6\left(f + \frac{1}{z^2}\right)^2 - \frac{g_2}{2} - \frac{6}{z^4} = 6f^2 + \frac{12 f}{z^2} - \frac{g_2}{2}.
$$

The nice thing is that the $$6/z^4$$ terms cancel exactly. Multiplying through by $$z^2$$ clears the last denominator:

\begin{equation}
z^2 f''(z) = 6 z^2 f(z)^2 + 12 f(z) - \frac{g_2}{2} z^2,
\end{equation}

where "$$f''$$" here means `deriv ℘'[L - 0]`. At $$z = 0$$ both sides are $$0$$ (the right because $$f(0) = 0$$), so the identity holds on a full neighbourhood of $$0$$. That last point matters. In section 7 we take $$n$$-th derivatives at $$0$$, and derivatives at $$0$$ "see" the value at $$0$$, so an identity on the punctured neighbourhood alone wouldn't be enough.

**The Lean.** `h1` proves the identity on the punctured neighbourhood. `hEq` rewrites `℘'[L - 0]` as the function $$w \mapsto \wp'(w) + 2/w^3$$ (using `funext` to go from a pointwise identity to an equality of functions). `hz3` differentiates $$2/w^3$$ using the quotient rule `HasDerivAt.div`. The rule outputs the derivative in the form $$(0 \cdot z^3 - 2 \cdot 3z^2)/(z^3)^2$$, so `convert h using 1` reduces the problem to showing that this equals $$-6/z^4$$, and `field_simp; ring` does the algebra (with `hz0` available to justify clearing denominators). `hsum` adds the two derivatives. Then we rewrite with `hEq`, the computed derivative, the differential equation `hD` from section 4, and the Laurent expansion `weierstrassP_eq`, and `field_simp; ring` checks the resulting rational identity.

`h2` proves the identity at the single point $$0$$. `pure 0` is the filter "at the point 0", and `eventually_pure` says that eventually along `pure 0` just means "at 0"; `simp` then evaluates both sides to $$0$$. The last two lines glue these together. `Filter.eventually_sup` says a property holds eventually along $$F \sqcup G$$ iff it does along both, and `nhdsNE_sup_pure` says the punctured neighbourhood filter joined with the point filter is the full neighbourhood filter.

**Why it works.** The derivation handles the singularity honestly. The algebra is done away from $$0$$, where everything is defined, and the value at $$0$$ is checked separately.

## 6. The Leibniz rule for z² g(z)

```
/-- Leibniz collapse: the `n`-th derivative of `z² g(z)` at `0` for analytic `g`. -/
lemma iteratedDeriv_sq_mul (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0) {n : ℕ} (hn : 2 ≤ n) :
    iteratedDeriv n (fun z : ℂ ↦ z ^ 2 * g z) 0 =
      (n : ℂ) * ((n : ℂ) - 1) * iteratedDeriv (n - 2) g 0 := by
  have e : iteratedDeriv n (fun z : ℂ ↦ z ^ 2 * g z) 0 =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv i (· ^ 2 : ℂ → ℂ) 0 *
        iteratedDeriv (n - i) g 0 :=
    iteratedDeriv_fun_mul (by fun_prop) hg.contDiffAt
  rw [e, Finset.sum_eq_single_of_mem 2 (Finset.mem_range.mpr (by omega))
    (fun i _ hi ↦ by rw [iteratedDeriv_fun_pow_zero, if_neg hi]; ring),
    iteratedDeriv_fun_pow_zero, if_pos rfl, Nat.cast_choose_two]
  norm_num [Nat.factorial_two]
```

**The maths.** By the Leibniz rule,

$$
\frac{d^n}{dz^n}\Big(z^2 g(z)\Big)\Big|_{z=0} = \sum_{i=0}^{n} \binom{n}{i} \left.\frac{d^i}{dz^i} z^2\right|_{z=0} g^{(n-i)}(0).
$$

The derivatives of $$z^2$$ at $$0$$ all vanish except the second, which is $$2$$. So only the $$i = 2$$ term survives, and $$2\binom{n}{2} = n(n-1)$$, giving $$n(n-1)\,g^{(n-2)}(0)$$.

**The Lean.** `iteratedDeriv_fun_mul` is Mathlib's Leibniz rule. It needs both factors to be smooth at the point: `fun_prop` handles $$z^2$$, and `hg.contDiffAt` converts the analyticity of $$g$$ into smoothness. `Finset.sum_eq_single_of_mem 2 h₁ h₂` collapses a sum to its $$i = 2$$ term, given `h₁ : 2 ∈ range (n + 1)` (true since $$n \geq 2$$, checked by `omega`) and `h₂`, saying every other term is zero. Both of these use Mathlib's `iteratedDeriv_fun_pow_zero`, which says the $$i$$-th derivative of $$z^m$$ at $$0$$ is `if i = m then m ! else 0`. Finally `Nat.cast_choose_two` rewrites $$\binom{n}{2}$$ as $$n(n-1)/2$$, and `norm_num` with $$2! = 2$$ cancels the halves.

**Why it works.** It's the Leibniz rule plus bookkeeping. The hypothesis $$n \geq 2$$ isn't really needed mathematically (for $$n = 0, 1$$ both sides are $$0$$), but it makes the sum collapse easy to state.

## 7. The recursion for the Taylor coefficients

```
/-- The recursion: for `n ≥ 3`, the `n`-th Taylor coefficient of `℘[L - 0]` at `0`
is determined by the earlier ones. -/
lemma recursion {n : ℕ} (hn : 3 ≤ n) :
    ((n : ℂ) * ((n : ℂ) - 1) - 12) * iteratedDeriv n ℘[L - (0 : ℂ)] 0 =
      6 * ((n : ℂ) * ((n : ℂ) - 1)) * ∑ k ∈ Finset.range (n - 1),
        ((n - 2).choose k : ℂ) * iteratedDeriv k ℘[L - (0 : ℂ)] 0 *
          iteratedDeriv (n - 2 - k) ℘[L - (0 : ℂ)] 0 := by
  have hfa : AnalyticAt ℂ ℘[L - (0 : ℂ)] 0 := L.analyticAt_weierstrassPExcept 0
  -- the `n`-th derivative of the left-hand side of `key_eventuallyEq`
  have hL : iteratedDeriv n (fun z : ℂ ↦ z ^ 2 * deriv ℘'[L - (0 : ℂ)] z) 0 =
      (n : ℂ) * ((n : ℂ) - 1) * iteratedDeriv n ℘[L - (0 : ℂ)] 0 := by
    rw [iteratedDeriv_sq_mul _ ((L.analyticAt_derivWeierstrassPExcept 0).deriv) (by omega)]
    congr 1
    rw [← iteratedDeriv_succ', show n - 2 + 1 = n - 1 by omega,
      L.iteratedDeriv_derivWeierstrassPExcept_self 0,
      L.iteratedDeriv_weierstrassPExcept_zero n, if_neg (by omega),
      show n - 1 + 2 = n + 1 by omega, show n - 1 + 3 = n + 2 by omega, sumInvPow_zero]
  -- the `n`-th derivative of the right-hand side, piece by piece
  have e1 : iteratedDeriv n (fun z : ℂ ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))
        + 12 * ℘[L - (0 : ℂ)] z - L.g₂ / 2 * z ^ 2) 0 =
      iteratedDeriv n (fun z : ℂ ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))
        + 12 * ℘[L - (0 : ℂ)] z) 0 - iteratedDeriv n (fun z : ℂ ↦ L.g₂ / 2 * z ^ 2) 0 :=
    iteratedDeriv_fun_sub (by fun_prop) (by fun_prop)
  have e2 : iteratedDeriv n (fun z : ℂ ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))
        + 12 * ℘[L - (0 : ℂ)] z) 0 =
      iteratedDeriv n (fun z : ℂ ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))) 0
        + iteratedDeriv n (fun z : ℂ ↦ 12 * ℘[L - (0 : ℂ)] z) 0 :=
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop)
  have e3 : iteratedDeriv n (fun z : ℂ ↦ L.g₂ / 2 * z ^ 2) 0 = 0 := by
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero, if_neg (by omega)]
    simp
  have e4 : iteratedDeriv n (fun z : ℂ ↦ 12 * ℘[L - (0 : ℂ)] z) 0 =
      12 * iteratedDeriv n ℘[L - (0 : ℂ)] 0 := by
    rw [iteratedDeriv_const_mul_field]
  have e5 : iteratedDeriv n
        (fun z : ℂ ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))) 0 =
      6 * ((n : ℂ) * ((n : ℂ) - 1) *
        iteratedDeriv (n - 2) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) 0) := by
    rw [iteratedDeriv_const_mul_field]
    congr 1
    exact iteratedDeriv_sq_mul _ (hfa.mul hfa) (by omega)
  have e6 : iteratedDeriv (n - 2) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) 0 =
      ∑ k ∈ Finset.range (n - 1), ((n - 2).choose k : ℂ) * iteratedDeriv k ℘[L - (0 : ℂ)] 0 *
        iteratedDeriv (n - 2 - k) ℘[L - (0 : ℂ)] 0 := by
    have e : iteratedDeriv (n - 2) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) 0 =
        ∑ k ∈ Finset.range (n - 2 + 1), ((n - 2).choose k : ℂ) *
          iteratedDeriv k ℘[L - (0 : ℂ)] 0 * iteratedDeriv (n - 2 - k) ℘[L - (0 : ℂ)] 0 :=
      iteratedDeriv_fun_mul hfa.contDiffAt hfa.contDiffAt
    rw [e, show n - 2 + 1 = n - 1 by omega]
  have key := L.key_eventuallyEq.iteratedDeriv_eq n
  rw [hL, e1, e2, e3, e4, e5, e6] at key
  linear_combination key
```

**The maths.** Take the $$n$$-th derivative at $$0$$ of both sides of the key identity. Using section 6 on each $$z^2(\cdots)$$ term, and the ordinary Leibniz rule for $$f^2$$, we get

$$
n(n-1)\, f^{(n)}(0) = 6\,n(n-1) \sum_{k=0}^{n-2} \binom{n-2}{k} f^{(k)}(0)\, f^{(n-2-k)}(0) + 12\, f^{(n)}(0) - \frac{g_2}{2}\cdot\left.\frac{d^n}{dz^n} z^2\right|_{z = 0}.
$$

For $$n \geq 3$$ the last term is $$0$$, and rearranging gives

\begin{equation}
\big(n(n-1) - 12\big)\, f^{(n)}(0) = 6\,n(n-1) \sum_{k=0}^{n-2} \binom{n-2}{k} f^{(k)}(0)\, f^{(n-2-k)}(0).
\end{equation}

Something I only noticed while writing this up: the coefficient on the left factorises as $$n(n-1) - 12 = (n-4)(n+3)$$. So it is nonzero for every $$n \geq 5$$ (and for $$n = 3$$), but it *vanishes at* $$n = 4$$. That's exactly why two invariants are needed. The recursion can't see $$f^{(4)}(0) = 5!\,G_6$$, so $$G_6$$, i.e. $$g_3$$, is genuinely extra data. The other piece of data, $$G_4$$, enters at $$n = 2$$, where the $$g_2 z^2$$ term does contribute: doing the same computation there gives $$10 f''(0) = g_2$$, which is consistent with $$f''(0) = 3!\,G_4$$ and $$g_2 = 60\,G_4$$.

As a sanity check, take $$n = 6$$. Using $$f(0) = f'(0) = f'''(0) = 0$$, only the $$k = 2$$ term survives and we get $$18\,f^{(6)}(0) = 180 \cdot 6 \cdot (3!\,G_4)^2$$, so $$f^{(6)}(0) = 2160\,G_4^2$$. Since $$f^{(6)}(0) = 7!\,G_8$$, this says $$G_8 = \tfrac{3}{7} G_4^2$$, which is the classical relation. Nice.

**The Lean.** The strategy is to compute the $$n$$-th derivative at $$0$$ of each side of `key_eventuallyEq`, and then compare them using `L.key_eventuallyEq.iteratedDeriv_eq n`. That is Mathlib's `Filter.EventuallyEq.iteratedDeriv_eq`: functions with the same germ at a point have the same iterated derivatives there. This is where it pays off that section 5 proved the identity on the full neighbourhood `𝓝 0`.

`hL` handles the left-hand side. Section 6 applied to $$g =$$ `deriv ℘'[L - 0]` gives $$n(n-1)$$ times the $$(n-2)$$-th derivative of `deriv ℘'[L - 0]`. `g` is analytic since the derivative of an analytic function is analytic (`AnalyticAt.deriv`). `congr 1` strips the common factor $$n(n-1)$$. Then `iteratedDeriv_succ'` (which says `iteratedDeriv (m + 1) f = iteratedDeriv m (deriv f)`), read backwards, turns the $$(n-2)$$-th derivative of `deriv ℘'[L - 0]` into the $$(n-1)$$-th derivative of `℘'[L - 0]`. At this point both sides have closed forms. Mathlib's `iteratedDeriv_derivWeierstrassPExcept_self` gives $$(n+1)!\,G_{n+2}$$ for the left, and our formula from section 2 gives the same for the right.

Interestingly, the proof never shows that `deriv ℘[L - 0] = ℘'[L - 0]` near $$0$$. It just checks that both sides match the same closed formula. Also, $$\mathbb{N}$$ subtraction is truncated ($$1 - 2 = 0$$), so rewriting needs the exact syntactic form; that's why there are little `show n - 2 + 1 = n - 1 by omega` steps. `omega` is a decision procedure for linear arithmetic over $$\mathbb{N}$$ and $$\mathbb{Z}$$ and has no trouble with truncated subtraction.

`e1` to `e6` take the right-hand side apart. `iteratedDeriv_fun_sub` and `iteratedDeriv_fun_add` split sums and differences, with `fun_prop` discharging the smoothness side conditions (this is where the local `fun_prop` attribute from section 1 is needed, to get from analyticity of $$f$$ to smoothness). `iteratedDeriv_const_mul_field` pulls out constants. `e3` kills the $$g_2 z^2$$ term, since $$n \neq 2$$. `e5` uses section 6 on $$z^2 f^2$$, and `e6` is the Leibniz rule for $$f \cdot f$$. After rewriting all of these into `key`, `linear_combination key` rearranges it into the stated recursion.

**Why it works.** After the derivatives are computed, what's left is linear algebra over $$\mathbb{C}$$, which `linear_combination` handles.

## 8. All coefficients are determined by g₂ and g₃

```
lemma iteratedDeriv_eq_of_invariants {L₁ L₂ : PeriodPair}
    (hg₂ : L₁.g₂ = L₂.g₂) (hg₃ : L₁.g₃ = L₂.g₃) (n : ℕ) :
    iteratedDeriv n ℘[L₁ - (0 : ℂ)] 0 = iteratedDeriv n ℘[L₂ - (0 : ℂ)] 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hG4 : L₁.G 4 = L₂.G 4 := by
      have h := hg₂
      simp only [g₂] at h
      exact mul_left_cancel₀ (by norm_num) h
    have hG6 : L₁.G 6 = L₂.G 6 := by
      have h := hg₃
      simp only [g₃] at h
      exact mul_left_cancel₀ (by norm_num) h
    rcases lt_or_ge n 5 with hn | hn
    · interval_cases n
      · simp [iteratedDeriv_weierstrassPExcept_zero]
      · simp [iteratedDeriv_weierstrassPExcept_zero,
          L₁.G_eq_zero_of_odd 3 (by decide), L₂.G_eq_zero_of_odd 3 (by decide)]
      · simp [iteratedDeriv_weierstrassPExcept_zero, hG4]
      · simp [iteratedDeriv_weierstrassPExcept_zero,
          L₁.G_eq_zero_of_odd 5 (by decide), L₂.G_eq_zero_of_odd 5 (by decide)]
      · simp [iteratedDeriv_weierstrassPExcept_zero, hG6]
    · have h₁ := L₁.recursion (n := n) (by omega)
      have h₂ := L₂.recursion (n := n) (by omega)
      have hsum : ∑ k ∈ Finset.range (n - 1), ((n - 2).choose k : ℂ) *
            iteratedDeriv k ℘[L₁ - (0 : ℂ)] 0 * iteratedDeriv (n - 2 - k) ℘[L₁ - (0 : ℂ)] 0 =
          ∑ k ∈ Finset.range (n - 1), ((n - 2).choose k : ℂ) *
            iteratedDeriv k ℘[L₂ - (0 : ℂ)] 0 *
              iteratedDeriv (n - 2 - k) ℘[L₂ - (0 : ℂ)] 0 :=
        Finset.sum_congr rfl fun k hk ↦ by
          have hk' := Finset.mem_range.mp hk
          rw [ih k (by omega), ih (n - 2 - k) (by omega)]
      have h20 : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      have hcoef : ((n : ℂ) * ((n : ℂ) - 1) - 12) ≠ 0 := by
        have hne : n * (n - 1) ≠ 12 := by omega
        have hc : ((n : ℂ) * ((n : ℂ) - 1) - 12) = ((n * (n - 1) : ℕ) : ℂ) - 12 := by
          push_cast [Nat.cast_sub (show 1 ≤ n by omega)]
          ring
        rw [hc, sub_ne_zero]
        exact_mod_cast hne
      apply mul_left_cancel₀ hcoef
      rw [h₁, h₂, hsum]
```

**The maths.** We show by strong induction on $$n$$ that $$f_{L_1}^{(n)}(0) = f_{L_2}^{(n)}(0)$$. First, $$g_2 = 60\,G_4$$ and $$g_3 = 140\,G_6$$, so equal invariants means equal $$G_4$$ and $$G_6$$.

- For $$n \leq 4$$, use the closed form $$f^{(n)}(0) = (n+1)!\,G_{n+2}$$. At $$n = 0$$ both sides are $$0$$. At $$n = 1, 3$$ they involve $$G_3, G_5$$, which are $$0$$. At $$n = 2, 4$$ they involve $$G_4, G_6$$, which agree.
- For $$n \geq 5$$, the recursion only involves $$f^{(k)}(0)$$ for $$k \leq n - 2$$, which agree by induction. Since $$(n-4)(n+3) \neq 0$$, we can divide and get $$f_{L_1}^{(n)}(0) = f_{L_2}^{(n)}(0)$$.

**The Lean.** `induction n using Nat.strong_induction_on` gives the strong induction hypothesis `ih : ∀ m < n, …`. `hG4` unfolds the definition of `g₂` with `simp only [g₂]`, turning `hg₂` into `60 * L₁.G 4 = 60 * L₂.G 4`, and cancels the $$60$$ with `mul_left_cancel₀`; `hG6` is the same with $$140$$. `rcases lt_or_ge n 5` splits into the two cases. For $$n < 5$$, `interval_cases n` produces the five goals $$n = 0, \ldots, 4$$, and each is a `simp` call with the closed form and the relevant fact about $$G$$ (`G_eq_zero_of_odd` for $$n = 1, 3$$). For $$n \geq 5$$, `hsum` shows the two sums in the recursions agree term by term (`Finset.sum_congr`), using `ih` twice. `omega` checks that $$k$$ and $$n - 2 - k$$ are below $$n$$.

`hcoef` is the fiddliest part, because the coefficient lives in $$\mathbb{C}$$ but the argument is about natural numbers. `omega` can't do nonlinear arithmetic, but given `h20 : 20 ≤ n(n-1)` as a fact about the product it can rule out $$n(n-1) = 12$$. `push_cast` with `Nat.cast_sub` moves the casts around (the subtraction cast needs $$1 \leq n$$), and `exact_mod_cast` finishes by transporting `hne` from $$\mathbb{N}$$ to $$\mathbb{C}$$. Finally, `mul_left_cancel₀ hcoef` cancels the coefficient and the two recursions `h₁`, `h₂` plus `hsum` close the goal.

**Why it works.** Every coefficient is given by a formula in strictly earlier coefficients with a nonzero denominator, so strong induction goes through. (Computing `hG4` and `hG6` inside the induction is a bit wasteful, as they don't depend on $$n$$, but it doesn't hurt anything.)

## 9. Same coefficients, same ℘ near 0

```
lemma weierstrassP_eventuallyEq {L₁ L₂ : PeriodPair}
    (h : ∀ n, iteratedDeriv n ℘[L₁ - (0 : ℂ)] 0 = iteratedDeriv n ℘[L₂ - (0 : ℂ)] 0) :
    ℘[L₁] =ᶠ[𝓝 (0 : ℂ)] ℘[L₂] := by
  have h₁ := (L₁.analyticAt_weierstrassPExcept 0).hasFPowerSeriesAt
  have h₂ := (L₂.analyticAt_weierstrassPExcept 0).hasFPowerSeriesAt
  have hp : (FormalMultilinearSeries.ofScalars ℂ
        fun n ↦ iteratedDeriv n ℘[L₁ - (0 : ℂ)] 0 / n !) =
      FormalMultilinearSeries.ofScalars ℂ
        fun n ↦ iteratedDeriv n ℘[L₂ - (0 : ℂ)] 0 / n ! := by
    congr 1
    funext n
    rw [h n]
  rw [hp] at h₁
  have hsub : HasFPowerSeriesAt (℘[L₁ - (0 : ℂ)] - ℘[L₂ - (0 : ℂ)])
      (0 : FormalMultilinearSeries ℂ ℂ ℂ) 0 := by
    simpa using h₁.sub h₂
  have hEq : ℘[L₁ - (0 : ℂ)] =ᶠ[𝓝 (0 : ℂ)] ℘[L₂ - (0 : ℂ)] := by
    filter_upwards [hsub.eventually_eq_zero] with z hz
    simpa [sub_eq_zero] using hz
  filter_upwards [hEq] with z hz
  rw [L₁.weierstrassP_eq z, L₂.weierstrassP_eq z, hz]
```

**The maths.** An analytic function equals its Taylor series near the point, so two analytic functions with the same Taylor coefficients agree near that point. So $$f_{L_1} = f_{L_2}$$ near $$0$$, and adding the common pole $$1/z^2$$ back gives $$\wp_{L_1} = \wp_{L_2}$$ near $$0$$.

**The Lean.** Mathlib's `AnalyticAt.hasFPowerSeriesAt` says an analytic function $$f$$ has power series $$\sum_n \frac{f^{(n)}(x)}{n!}(z - x)^n$$ at $$x$$, packaged as `FormalMultilinearSeries.ofScalars ℂ (fun n ↦ iteratedDeriv n f x / n !)`. `hp` shows the two series are equal using `h`, and after `rw [hp] at h₁` both functions have literally the same series. Then `h₁.sub h₂` says the difference has series "$$p - p$$", which `simpa` simplifies to the zero series. Mathlib's `HasFPowerSeriesAt.eventually_eq_zero` says a function with zero power series is zero near the point. The last two lines add $$1/z^2$$ back using `weierstrassP_eq`.

**Why it works.** This is uniqueness of power series expansions, which Mathlib already has in exactly the form we need.

## 10. Extending to the complement of both lattices

```
lemma eqOn_weierstrassP {L₁ L₂ : PeriodPair} (hev : ℘[L₁] =ᶠ[𝓝 (0 : ℂ)] ℘[L₂]) :
    Set.EqOn ℘[L₁] ℘[L₂] ((L₁.lattice : Set ℂ) ∪ (L₂.lattice : Set ℂ))ᶜ := by
  have hc₁ : (L₁.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L₁.lattice)
  have hc₂ : (L₂.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L₂.lattice)
  have hct := hc₁.union hc₂
  have hpre : IsPreconnected ((L₁.lattice : Set ℂ) ∪ (L₂.lattice : Set ℂ))ᶜ :=
    (hct.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  obtain ⟨U, hUs, hUo, h0U⟩ := mem_nhds_iff.mp hev
  obtain ⟨z₀, hz₀c, hz₀U⟩ := (hct.dense_compl ℂ).exists_mem_open hUo ⟨0, h0U⟩
  have hev' : ℘[L₁] =ᶠ[𝓝 z₀] ℘[L₂] := by
    filter_upwards [hUo.mem_nhds hz₀U] with z hz
    exact hUs hz
  exact (L₁.analyticOnNhd_weierstrassP.mono
      (Set.compl_subset_compl.mpr Set.subset_union_left)).eqOn_of_preconnected_of_eventuallyEq
    (L₂.analyticOnNhd_weierstrassP.mono
      (Set.compl_subset_compl.mpr Set.subset_union_right)) hpre hz₀c hev'
```

**The maths.** Let $$\Omega = \mathbb{C} \setminus (L_1 \cup L_2)$$. Both $$\wp$$ functions are analytic on $$\Omega$$. $$\Omega$$ is connected, since removing a countable set from $$\mathbb{C} \cong \mathbb{R}^2$$ can't disconnect it (you can always route a path around countably many points). The identity theorem says that two analytic functions on a connected open set which agree near one point of it agree everywhere on it. The one catch is that $$0$$ lies in both lattices, so $$0 \notin \Omega$$. Instead we pick a point $$z_0 \in \Omega$$ inside the neighbourhood of $$0$$ where the functions already agree. Such a point exists because $$\Omega$$ is dense.

**The Lean.** Each lattice is countable by `countable_of_Lindelof_of_discrete`: Mathlib knows the lattice is discrete and proper (hence Lindelöf), and a discrete Lindelöf space is countable. `Set.Countable.isConnected_compl_of_one_lt_rank` gives connectedness of the complement of a countable set in a real vector space of dimension more than $$1$$, where the dimension condition $$1 < \dim_{\mathbb{R}} \mathbb{C} = 2$$ is `by simp`.

`mem_nhds_iff` unpacks `hev` into an open set `U ∋ 0` on which the functions agree. `Set.Countable.dense_compl ℂ` says $$\Omega$$ is dense, and `Dense.exists_mem_open` finds `z₀ ∈ Ω ∩ U`. `hev'` repackages agreement on `U` as agreement near `z₀`. The last step is Mathlib's identity theorem, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`. We need analyticity of both functions on $$\Omega$$, and Mathlib gives analyticity of $$\wp_{L_i}$$ on $$\mathbb{C} \setminus L_i$$; `.mono` restricts that to the smaller set $$\Omega$$.

**Why it works.** This is the identity theorem, and the only real work is the topology of $$\Omega$$ (connected and dense), which Mathlib handles.

## 11. The poles recover the lattice

```
lemma lattice_le_of_eqOn {L₁ L₂ : PeriodPair}
    (h : Set.EqOn ℘[L₁] ℘[L₂] ((L₁.lattice : Set ℂ) ∪ (L₂.lattice : Set ℂ))ᶜ) :
    L₁.lattice ≤ L₂.lattice := by
  intro x hx
  by_contra hx₂
  have hev : ℘[L₁] =ᶠ[𝓝[≠] x] ℘[L₂] := by
    have hW : ((L₂.lattice : Set ℂ))ᶜ ∩ ((L₁.lattice : Set ℂ) \ {x})ᶜ ∈ 𝓝 x :=
      Filter.inter_mem (L₂.isClosed_lattice.isOpen_compl.mem_nhds hx₂)
        (L₁.compl_lattice_diff_singleton_mem_nhds x)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hW, self_mem_nhdsWithin]
      with z hz (hzx : z ≠ x)
    obtain ⟨hz₂, hz₁⟩ := hz
    refine h ?_
    rintro (hzL | hzL)
    · exact hz₁ ⟨hzL, hzx⟩
    · exact hz₂ hzL
  have h₁ : meromorphicOrderAt ℘[L₁] x = -2 := L₁.order_weierstrassP x hx
  have h₂ : (0 : WithTop ℤ) ≤ meromorphicOrderAt ℘[L₂] x :=
    (L₂.analyticOnNhd_weierstrassP x hx₂).meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr hev, h₁] at h₂
  exact absurd h₂ (by decide)
```

**The maths.** Suppose $$x \in L_1$$ but $$x \notin L_2$$. Near $$x$$, but not at $$x$$, there are no points of $$L_1$$ (discreteness) and no points of $$L_2$$ ($$L_2$$ is closed and $$x \notin L_2$$), so the two $$\wp$$ functions agree on a punctured neighbourhood of $$x$$. But $$\wp_{L_1}$$ has a double pole at $$x$$, while $$\wp_{L_2}$$ is analytic at $$x$$. Functions that agree on a punctured neighbourhood have the same order there, so $$-2 \geq 0$$, a contradiction.

**The Lean.** `L₁.lattice ≤ L₂.lattice` means `∀ x ∈ L₁, x ∈ L₂`, so `intro x hx` works directly, and `by_contra hx₂` assumes `x ∉ L₂`. `hW` is the neighbourhood from the maths: the complement of $$L_2$$ intersected with the complement of $$L_1 \setminus \{x\}$$. It's the intersection of two neighbourhoods of $$x$$ (`Filter.inter_mem`). After `filter_upwards`, `refine h ?_` reduces agreement at `z` to showing `z` is outside the union, and `rintro (hzL | hzL)` does case analysis on "`z` is in the union".

Mathlib measures poles and zeros with `meromorphicOrderAt f x : WithTop ℤ`, where the `⊤` is for functions that vanish near $$x$$. Mathlib's `order_weierstrassP` gives order $$-2$$ at lattice points. `AnalyticAt.meromorphicOrderAt_nonneg` gives order $$\geq 0$$ at points where the function is analytic. `meromorphicOrderAt_congr` says the order only depends on the function on a punctured neighbourhood, so rewriting `h₂` with it and `h₁` turns it into `0 ≤ -2`. `decide` evaluates that in `WithTop ℤ` and finds it false.

**Why it works.** The order is an invariant of the germ on a punctured neighbourhood, and it tells lattice points apart from non-lattice points.

## 12. The main theorem

```
/-- **Uniqueness theorem for complex lattices**: a period lattice is determined by
its invariants `g₂` and `g₃`. -/
theorem lattice_eq_of_g₂_eq_of_g₃_eq {L₁ L₂ : PeriodPair}
    (hg₂ : L₁.g₂ = L₂.g₂) (hg₃ : L₁.g₃ = L₂.g₃) : L₁.lattice = L₂.lattice := by
  have hEqOn := eqOn_weierstrassP
    (weierstrassP_eventuallyEq (iteratedDeriv_eq_of_invariants hg₂ hg₃))
  refine le_antisymm (lattice_le_of_eqOn hEqOn) (lattice_le_of_eqOn ?_)
  rw [Set.union_comm]
  exact fun z hz ↦ (hEqOn hz).symm

/-- The classical uniqueness theorem: a period lattice is determined by its invariants
`g₂`, `g₃`. Its formalization (via the Laurent expansion of `℘` and the recursion for the
`G`-sums induced by `℘'² = 4℘³ - g₂℘ - g₃`) -/
theorem invariantsDetermineLattice :
    ∀ L₁ L₂ : PeriodPair, L₁.g₂ = L₂.g₂ → L₁.g₃ = L₂.g₃ → L₁.lattice = L₂.lattice :=
  fun _ _ => lattice_eq_of_g₂_eq_of_g₃_eq
```

**The maths.** Chain everything together. Equal invariants give equal Taylor coefficients (section 8), which give equal $$\wp$$ near $$0$$ (section 9), which gives equal $$\wp$$ off both lattices (section 10). Then section 11 gives $$L_1 \subseteq L_2$$, and by symmetry $$L_2 \subseteq L_1$$.

**The Lean.** The first line is the whole chain as nested function applications. `le_antisymm` proves equality from the two inclusions. For the reverse inclusion, `lattice_le_of_eqOn` wants agreement of `℘[L₂]` and `℘[L₁]` on the complement of $$L_2 \cup L_1$$. `rw [Set.union_comm]` swaps the union round, and `(hEqOn hz).symm` swaps the equality round. `invariantsDetermineLattice` is the same theorem with the lattices as explicit arguments. In `fun _ _ =>` the underscores are just unused names for those two arguments, and Lean fills in the implicit `L₁`, `L₂` of `lattice_eq_of_g₂_eq_of_g₃_eq` by unification.

## Summary

Each lemma lines up with a step of the classical proof.

1. Laurent expansion (section 2): $$\wp = 1/z^2 + f$$ with $$f^{(n)}(0) = (n+1)!\,G_{n+2}$$.
2. Differential equations (sections 3 to 5): $$(\wp')^2 = 4\wp^3 - g_2\wp - g_3$$ gives $$\wp'' = 6\wp^2 - g_2/2$$ and then the pole-free identity $$z^2 f'' = 6z^2f^2 + 12f - \tfrac{g_2}{2}z^2$$.
3. Recursion (sections 6 to 8): $$(n-4)(n+3) f^{(n)}(0)$$ is a polynomial in earlier coefficients, so everything is determined by $$G_4$$ and $$G_6$$.
4. Local equality (section 9): equal Taylor coefficients give equal $$\wp$$ near $$0$$.
5. Global equality (section 10): the identity theorem on the connected set $$\mathbb{C} \setminus (L_1 \cup L_2)$$.
6. Recovering the lattice (sections 11 and 12): lattice points are exactly the poles.

## Looking back

Going back over the code for this write-up, there are a few things I'd tidy up. The biggest is section 3. Rather than bounding norms by hand, it's enough to notice that $$z \mapsto z^3\,\wp'_{L \setminus 0}(z) - 2$$ is analytic and equals $$-2$$ at $$0$$, so by continuity it's nonzero near $$0$$, and that already forces $$\wp' \neq 0$$. This is the same pole-clearing trick Mathlib uses to prove the differential equation in the first place, and it cuts the proof down to a few lines. In section 5, Mathlib has a lemma, `eventuallyEq_nhds_of_eventuallyEq_nhdsNE`, which does the "punctured neighbourhood plus the point itself" step in one go. That would also save stating the whole identity twice. The lemma `compl_lattice_diff_singleton_mem_nhds` has also since been renamed to `compl_lattice_sdiff_singleton_mem_nhds` in Mathlib, and the docstring on `invariantsDetermineLattice` just trails off mid-sentence, which does annoy me a little.

Going forward, the natural next step would be the converse. For any $$g_2, g_3 \in \mathbb{C}$$ with $$g_2^3 - 27g_3^2 \neq 0$$ there should exist a lattice with those invariants. This is the harder direction (it's where the uniformisation theorem for elliptic curves comes in), and combined with what's here it would give a bijection between lattices and pairs $$(g_2, g_3)$$ with nonzero discriminant. I'm not sure how much of the machinery for that exists in Mathlib yet, but it would be a nice thing to try.
