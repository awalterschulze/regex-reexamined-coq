![Check Proofs](https://github.com/awalterschulze/regex-reexamined-coq/workflows/Check%20Proofs/badge.svg)

# Derivatives for Regular reexamined with Coq

This repo reexamines a few papers on regular expressions using Coq as a learning exercise.
We try to prove some things that are mentioned in the papers as a way to teach ourselves some Coq.

  - [Regular-expression derivatives reexamined](./src/Reexamined)
    This paper is a great introduction to using derivatives for regular expressions,
    since it has been not only been updated, but is also one of the easier papers to read.
  - [Derivatives of Regular Expressions - Janusz A Brzozowski](./src/Brzozowski)
    This is the original paper on regular expressions.
    We have retyped and modified it a bit to aid readability.
  - [CoqStock](./src/CoqStock) standard library.

## Setup

1. Install Coq 8.12.0
2. Remember to set coq in your PATH. For example, in your `~/.bash_profile` add `PATH="/Applications/CoqIDE_8.12.0.app/Contents/Resources/bin/:${PATH}"` and run `$ source ~/.bash_profile`.
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

Join us in a pair programming session. The schedule is posted as meetups events on [meetup.com](https://www.meetup.com/London-TyDD/)
