# To Mock a Mockingbird

This repository contains the solutions of the puzzles from the book *To Mock a Mockingbird and other logic puzzles* by Raymond Smullyan, using the theorem prover [Lean](https://leanprover-community.github.io/) (3.8).

Staring from Chapter 9, Smullyan introduces combinatory logic by an analogy to birds.

For any bird, we can call the name of another bird and it will respond with another bird.

In Lean, a bird can be modeled as a type with a constructor that takes 2 birds: the bird in question, the bird being called and the bird used as response.

  inductive Bird
    | Call : Bird -> Bird -> Bird
  open Bird

From this simple construct it's possible to derive very interesting properties.
