Contributions are welcome!

If you start formalizing any of the results mentioned in the blueprint, please announce this on Zulip first, in the (to be created) Carleson channel. Small fixes are always welcome, and need not be discussed in advance.

Simply make a pull request with a change.

Some remarks:
* Some statements will be missing hypotheses. Don't hesitate adding hypotheses to a result, especially if it is already assumed elsewhere. Assuming that functions are measurable is always fine.
* Many results have a constant in front of them. We put these constants in a separate def,
  so that the proofs hopefully break slighlty less easily.
  Feel free to improve these constants
  - either just write a comment in the Lean file that the constant can be improved to X
  - or improve the constant in Lean with a comment that this has to be incorporated in the blueprint
  - or improve the constant both in Lean and the TeX file, making sure you also fix all downstream uses of the lemma.
