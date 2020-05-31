# agda-analysis

Formalization in Agda of the material in _Analysis I_, the real
analysis textbook by Terence Tao.

## Setup

This project depends upon the Agda standard library, as well as the
[agda-axiomatic](https://github.com/cruhland/agda-axiomatic) library
which is where many of the definitions and proofs from the textbook
are actually located. Since the material is useful beyond solving
textbook exercises, keeping it independent of the book's structure
just made sense.

You'll need to make sure those libraries are available on your system
before you can build this project's code; see [Library
Management](https://agda.readthedocs.io/en/latest/tools/package-system.html)
in the Agda documentation for instructions.
