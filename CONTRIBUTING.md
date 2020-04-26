# Contributing Guidelines

## How to start

1. Create a pull request on master
2. Make sure the github action that automatically checks your proofs passes.
3. Wait for at least one approval from a reviewer
4. Merge (or poke for a merge, depending on your permissions)
5. Add yourself to the AUTHORS file

## FAQ

### Where to jump in

1. Find a TODO or Admitted or Abort proof and try to prove it.
2. Read the paper and find something we haven't proved yet.
3. Open an github issue, if you would like to prove something different that you still feels belong here.

### I have an alternative proof

The more the merrier.

We welcome alternative proofs.  Please submit your proof with a new name, by adding a tick `'` at the end of the function name.

Reason: This is a learning repo and seeing alternatives to the same proof is helpful.  This is not just helpful in pull requests, but also to new comers to the repo and that is why it is still useful to merge them into master.

### Comments

 - Do we like comments? Yes we do.
 - Are they required? No.

### When to use a separate file

Now.  When you are starting to ask this question, it is time to start using a separate file. Please make sure to add it to the Makefile, so that the proofs are checked in the pull request.

### TODO, Admitted and Abort

Yes we can merge an Admitted or Abort proof with a TODO comment.  This is where reviewing the code is important.  We need to believe that the Admitted proof is provable by us in future and we prefer an Abort proof as a way of documenting an interesting theorem to prove, but we understand that sometimes an Admitted proof is needed.

A proof may be left out if:

 - you are lazy, for example maybe you see the proof will be similar to other proofs (this gives beginners an opportunity to also contribute).  In this case please add `(* TODO: Good First Issue *)`
 - you need help (this gives beginners who are up for a challenge, a chance to contribute). In this case please add `(* TODO: Help Wanted *)`
