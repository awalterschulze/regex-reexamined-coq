![Check Proofs](https://github.com/awalterschulze/regex-reexamined-coq/workflows/Check%20Proofs/badge.svg)

**This learning exercise has come to an end, we are continuing work in this [here](https://github.com/katydid/proofs)**

# Derivatives for Regular reexamined with Coq

This repo reexamines a few papers on regular expressions using Coq as a learning exercise.
We try to prove some things that are mentioned in the papers as a way to teach ourselves some Coq.

  - [Brzozowski](./src/Brzozowski)
    In this folder we explore proving theorems from the original paper [Derivatives of Regular Expressions - Janusz A Brzozowski](./src/Brzozowski/Derivatives%20of%20Regular%20Expressions%20-%20Janusz%20A%20Brzozowski.md)
    We have retyped and modified it a bit to aid readability.
  - [Coinduction](./src/Coinduction)
    In this folder we explore using coinduction to prove regular expressions are equivalent.
  - [Reexamined](./src/Reexamined)
    In this folder we explore a modern version of derivatives defined in the paper [Regular-expression derivatives reexamined](https://www.ccs.neu.edu/home/turon/re-deriv.pdf)
    This paper is a great introduction to using derivatives for regular expressions,
    since it has been not only been updated, but is also one of the easier papers to read.
  - [CoqStock](./src/CoqStock) standard library.

## Setup

1. Install Coq 8.13.0
2. Remember to set coq in your PATH. For example, in your `~/.bash_profile` add `PATH="/Applications/CoqIDE_8.13.0.app/Contents/Resources/bin/:${PATH}"` and run `$ source ~/.bash_profile`.
3. Run make in this folder.

Note:

 - `make cleanall` cleans all files even `.aux` files.

## Contributing

Please read the [contributing guidelines](https://github.com/awalterschulze/regex-reexamined-coq/blob/master/CONTRIBUTING.md).  They are short and shouldn't be surprising.

## Regenerate Makefile

Coq version upgrade requires regenerating the Makefile with the following command:

```
$ coq_makefile -f _CoqProject -o Makefile
```

## Pair Programming

We used to pair program. The schedule was posted as meetups events on [meetup.com](https://www.meetup.com/London-TyDD/)
