# formalizingprobability-lean

## Ballot theorem proof strategy

The proof strategy is mine: split bad paths by their first step, pair the two
groups by reflecting each path up to its first return to 0, and count the
remaining good paths to obtain the probability.

This is the original six-step plan I wrote on paper before formalizing the
proof in Lean. It shows the idea behind the argument.

![Notes] (notes.png)

The Lean syntax was written with AI assistance.