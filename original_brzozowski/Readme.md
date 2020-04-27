# Derivatives of Regular Expressions - Janusz A Brzozowski

This folder contains the original paper for [Derivatives of Regular Expressions - Janusz A Brzozowski](./Derivatives%20of%20Regular%20Expressions%20-%20Janusz%20A%20Brzozowski.md)

We also redefine regular expressions in this folder in terms of this original paper.
The goal of this folder, is to prove Theorem 4.3 (a).

The included paper has some modifications, to help it easier to read and use, these include:

  - rewritten in markdown
  - removal of some less interesting parts:
    + references to Mealy model
    + section 6
  - rephrased A_k as Sigma_k, to make it clear that Sigma_k is the input alphabet
  - renamings of variables
  - some extra explanations

This markdown is then rerendered to pdf using pandoc [here](./Derivatives%20of%20Regular%20Expressions%20-%20Janusz%20A%20Brzozowski.pdf)

The real original paper can be found [here](http://maveric.uwaterloo.ca/reports/1964_JACM_Brzozowski.pdf)

## Regeneration

  - Install pandoc
  - Install xelatex
  - run `$ make`