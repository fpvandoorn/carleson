Contributions are welcome!

If you start formalizing any of the results mentioned in the blueprint, please announce this on Zulip first, in the (to be created) Carleson channel. Small fixes are always welcome, and need not be discussed in advance. Simply make a pull request with a change.

Some remarks:
* Some statements will be missing hypotheses. Don't hesitate adding hypotheses to a result, especially if it is already assumed elsewhere. Assuming that functions are measurable is always fine.
* Please add small additional lemmas liberally.
* Some statements might need to be modified, or additional lemmas added. E.g. some estimates about norms or `ENNReal.toReal` will need a separate statement that the value is (almost everywhere) finite.
* Feel free to change definitions/theorem statements to more convenient versions. Especially when deciding to put (in)equalities in `ℝ≥0∞`, `ℝ≥0` or `ℝ`, it is hard to know what is most convenient in advance.
* With suprema, it's probably most convenient to take suprema over `ℝ≥0∞`, and potentially apply `ENNReal.toReal` afterwards.
* Many inequalities are up to some constant factor (depending on `a` and `q`).
  We put these constants in a separate definition, so that the proofs hopefully break slighlty less easily.
  *If you prove a theorem with a constant used other theorems with constants, it is **encouraged**
  to define your constant in terms of the other constants, and to not unfold the constants of the other theorems*.

  Feel free to improve these constants:
  - either just write a comment in the Lean file that the constant can be improved to X
  - or improve the constant in Lean with a comment that this has to be incorporated in the blueprint
  - or improve the constant both in Lean and the TeX file, making sure you also fix all downstream uses of the lemma.
* If you are writing lemma statements yourself, make sure to look at the class [`ProofData`](http://florisvandoorn.com/carleson/docs/Carleson/Defs.html#ProofData), which contains a lot of the common data/assumptions used throughout sections 2-8.

Below, I will try to give a translation of some notation/conventions. We use mathcal/mathfrak unicode characters liberally to make the Lean look similar to the blueprint.

| Blueprint | Lean       | Remarks |
| --------- | ---------- | ------- |
| `⊂`       | `⊆`       |         |
| `𝔓(𝔓')`   | `lowerClosure 𝔓'` |         |
| `λp ≲ λ'p'`   | `smul l p ≤ smul l' p' ` |         |
| `p ≲ p'`   | `smul 1 p ≤ smul 1 p' ` | Beware that this is not the same as `p ≤ p'`. |
| `d_B(f,g)`   | `dist_{x, r} f g` | Assuming `B = B(x,r)` is the ball with center `x` and radius `r`. Lean also has the variants `nndist_` and `ball_`. |
| `d_{Iᵒ}(f,g)`   | `dist_{I} f g` |  |
| `d_{𝔭}(f,g)`   | `dist_(𝔭) f g` | `d_{𝔭}(f,g) = d_{𝓘(p)ᵒ}(f,g)`. |
| `Kₛ(x, y)`       | `Ks s x y`       |         |
| `T_*f(x)`       | `ANCZOperator K f x`       | The associated nontangential Calderon Zygmund operator |
| `Tf(x)`       | `CarlesonOperator K f x` | The generalized Carleson operator        |
| `Tₚf(x)`       | `T p f x`       |         |
| `e(x)`       | `Complex.exp (Complex.I * x)` |         |
| `𝔓(I)`       | `𝓘 ⁻¹' {I}` |         |
|         |       |         |
