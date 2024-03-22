# carleson
A (WIP) formalized proof of Carleson's theorem in Lean

## Contribute

To get the repository, make sure you have [installed Lean](https://leanprover-community.github.io/get_started.html). Then get the repository using `git clone https://github.com/fpvandoorn/carleson.git` and run `lake exe cache get` inside the repository. Run `lake build` to build all files in this repository. See the README of [my course repository](https://github.com/fpvandoorn/LeanCourse23) for more detailed instructions.

To publish your changes on Github, you need to be added as a contributor to this repository. Make a Github account if you don't have one already and send your Github account per email to Floris. I will add you.

To push your changes, the easiest method is to use the `Source Control` panel in VSCode.
Feel free to push unfinished code and code that is work in progress, but make sure that the file(s)
you've worked have no errors (having `sorry`'s is of course fine).

## Build the blueprint

To build the web version of the blueprint, you need a working LaTeX installation.
Furthermore, you need some packages:
```
sudo apt install graphviz libgraphviz-dev
pip3 install invoke pandoc
cd .. # go to folder where you are happy clone git repos
git clone git@github.com:plastex/plastex
pip3 install ./plastex
git clone git@github.com:PatrickMassot/leanblueprint
pip3 install ./leanblueprint
cd sphere-eversion
```

To actually build the blueprint, run
```
lake exe cache get
lake build
inv all
```

To view the web-version of the blueprint locally, run `inv serve` and navigate to
`http://localhost:8000/` in your favorite browser.