# Formalization of a generalized Carleson's theorem
A formalized proof of a generalized Carleson's theorem in Lean.

## What is Carleson's theorem?

Carleson's theorem is a statement about Fourier analysis: given a continuous periodic function $f\colon ℝ → ℝ$, its Fourier converges to $f$ point-wise at almost every point.
More precisely, let $f\colon\mathbb{R} → \mathbb{C}$ be a $2\pi$-periodic bounded Borel measurable function.
For each integer $n\in\mathbb{Z}$, define the $n$-th Fourier coefficient as
\[ \widehat{f}_n:=\frac {1}{2\pi} \int_0^{2\pi} f(x) e^{- i nx} dx. \]
For $N\geq 0$, define the partial Fourier sum as
\[ s_Nf(x):=\sum_{n=-N}^N \widehat{f}_n e^{i nx}. \]
Then Carleson's theorem states $\lim_{N\to\infty} s_N f(x) = f(x)$ for almost all $x\in\mathbb{R}$.

Despite being simple to state, its proof is very hard. (It is also quite subtle: for instance, asking for point-wise convergence *everywhere* makes this false.)

## How do we prove it?

In this project, we deduce this statement from the boundedness of a certain linear operator, the so-called *Carleson operator*.
This boundedness holds in much greater generality: we formalise a new generalisation (due to Christoph Thiele and his group) to [doubling metric measure spaces](https://florisvandoorn.com/carleson/docs/Carleson/ToMathlib/DoublingMeasure.html#MeasureTheory.DoublingMeasure).

The main technical result we prove is the following.
To keep this exposition short, we refer to the [introduction](https://florisvandoorn.com/carleson/blueprint/sect0001.html) for the main set-up and notation, and merely note that $T$ is the generalised Carleson operator whose boundedness is instrumental for proving Carleson's theorem.

**Metric space Carleson theorem**
For all integers $a \ge 4$ and real numbers $1<q\le 2$ the following holds.
Let $(X,\rho,\mu,a)$ be a doubling metric measure space.
Let $\Mf$ be a cancellative compatible collection of functions and let $K$ be a one-sided Calder\'on--Zygmund kernel on $(X,\rho,\mu,a)$. Assume that for every bounded measurable function $g$ on $X$ supported on a set of finite measure we have
\[ \|T_{*}g\|_{2} \leq 2^{a^3} \|g\|_2\,, \]
where $T_{*}$ is defined in \eqref{def-tang-unm-op}.
Then for all Borel sets $F$ and $G$ in $X$ and all Borel functions $f:X\to \C$ with $|f|\le \mathbf{1}_F$, we have, with $T$ defined in \eqref{def-main-op},
\[ \left|\int_{G} T f \, \mathrm{d}\mu\right| \leq \frac{2^{443a^3}}{(q-1)^6} \mu(G)^{1-\frac{1}{q}} \mu(F)^{\frac{1}{q}}\, . \]

The third main result allows proving a generalisation of Carleson's theorem to **Walsh functions.**
Again, we refer the reader to the [introduction](https://florisvandoorn.com/carleson/blueprint/sect0001.html) for the set-up and notation.

**Linearised metric space Carleson theorem.**
For all integers $a \ge 4$ and real numbers $1<q\le 2$ the following holds.
Let $(X,\rho,\mu,a)$ be a doubling metric measure space. Let $\Mf$ be a cancellative compatible collection of functions.
Let $\tQ:X\to \Mf$ be a Borel function with finite range.
Let $K$ be a one-sided Calder\'on--Zygmund kernel on $(X,\rho,\mu,a)$. Assume that for every $\mfa\in \Mf$ and every bounded measurable function $g$ on $X$ supported on a set of finite measure we have
\[ \|T_{\tQ}^\mfa g\|_{2} \leq 2^{a^3} \|g\|_2\,, \]
where $T_{\tQ}^\mfa$ is defined in \eqref{def-lin-star-op}.
Then for all Borel sets $F$ and $G$ in $X$ and all Borel functions $f:X\to \C$ with $|f|\le \mathbf{1}_F$, we have, with $T_\tQ$ defined in \eqref{def-lin-main-op},
\[ \left|\int_{G} T_\tQ f \, \mathrm{d}\mu\right| \le \frac{2^{443a^3}}{(q-1)^6} \mu(G)^{1-\frac{1}{q}} \mu(F)^{\frac{1}{q}}\, . \]

## Verifying the formalisation

This proof has been formalised in the Lean theorem prover. To confirm the correctness and completeness yourself, follow these steps.
1. Make sure you have [installed Lean](https://leanprover-community.github.io/get_started.html).
2. Download the repository using `git clone https://github.com/fpvandoorn/carleson.git`.
3. Open the directory where you downloaded the repository (but not any further sub-directory). Open a terminal in this directory and run `lake exe cache get!` to download built dependencies. (This step is not required, but speeds up the build process in the next steps.)
4. Determine which Lean statement you want to verify: the Lean statements of the main theorems above are `classical_carleson`, `metric_carleson` and `linearized_metric_carleson`, respectively.
metric_carleson. Open the file `Carleson/Carleson.lean` in a text editor of your choice. Add the end of the file, add a line `#print axioms linearized_metric_carleson` (or similar). This will tell Lean to verify that the proof of this result was completed correctly.
5. In the terminal from step 3, run `lake build` to build all files in this repository. This may take a few minutes.
When the process is complete, at the very end of the output, you will see a line `'linearized_metric_carleson' depends on axioms: [propext, Classical.choice, Quot.sound]` (followed by `Build completed successfully`).
This shows the proof is complete and correct. Had the build failed or the output included `sorryAx`, this would have indicated an error resp. an incomplete proof.
(For the experts: this shows which axioms Lean used in the course of the proof. `propext` and `Quot.sound` are built into Lean's type theory, `Classical.choice` tells you that Lean's version of the axiom of choice was used.)

## Contribute

* [Zulip channel](https://leanprover.zulipchat.com/#narrow/stream/442935-Carleson) for coordination
* [Webpage](https://florisvandoorn.com/carleson/)
* [Blueprint](https://florisvandoorn.com/carleson/blueprint/)
* [Blueprint as pdf](https://florisvandoorn.com/carleson/blueprint.pdf)
* [Dependency graph](https://florisvandoorn.com/carleson/blueprint/dep_graph_document.html)
* [Documentation pages for this repository](https://florisvandoorn.com/carleson/docs/)

### Locally

1. Make sure you have [installed Lean](https://leanprover-community.github.io/get_started.html).
2. Download the repository using `git clone https://github.com/fpvandoorn/carleson.git`.
3. Run `lake exe cache get!` to download built dependencies (this speeds up the build process).
4. Run `lake build` to build all files in this repository.

See the README of [my course repository](https://github.com/fpvandoorn/LeanCourse23) for more detailed instructions.

### In github codespaces

If you prefer, you can use online development environment:

<a href="https://codespaces.new/fpvandoorn/carleson"><img src="https://github.com/codespaces/badge.svg"/></a>

To make changes to this repository, please make a pull request. There are more tips in the file [Contributing.md](https://github.com/fpvandoorn/carleson/blob/master/CONTRIBUTING.md). To push your changes, the easiest method is to use the `Source Control` panel in VSCode.
Feel free to make pull requests with code that is work in progress, but make sure that the file(s)
you've worked have no errors (having `sorry`'s is fine of course).

## Build the blueprint

To test the Blueprint locally, you can compile `print.tex` using XeLaTeX (i.e. `xelatex print.tex` in the folder `blueprint/src`). If you have the Python package `invoke` you can also run `inv bp` which puts the output in `blueprint/print/print.pdf`.
If you want to build the web version of the blueprint locally, you need to install some packages by following the instructions [here](https://pypi.org/project/leanblueprint/). But if the pdf builds locally, you can also just make a pull request and use the online blueprint.
