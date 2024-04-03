---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

{% include mathjax.html %}

# Carleson's theorem

WIP formalization of a generalized Carleson's theorem

* [Blueprint of the proof](https://florisvandoorn.com/carleson/blueprint/)
* [Blueprint (pdf)](https://florisvandoorn.com/carleson/blueprint.pdf)
* [Documentation of the methods](https://florisvandoorn.com/carleson/docs/)

## Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html) (under Regular install).

To build the project, run `lake exe cache get` and then `lake build`.

## Build the blueprint

The blueprint is automatically built on each push to the project.
You can test whether the build is working by building the pdf locally:
`xelatex blueprint/src/print.tex`.

<!-- To build the web version of the blueprint locally, you need a working LaTeX installation.
Furthermore, you need some packages:
```
sudo apt install graphviz libgraphviz-dev
pip install -r blueprint/requirements.txt
```

To actually build the blueprint, run
```
lake exe cache get
lake build
inv all
``` -->
