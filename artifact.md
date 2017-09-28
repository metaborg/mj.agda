# Contents

src/ScopeGraph

src/STLC
src/STLCRef
src/STLCSF
src/MJSF -- contains two semantics: one that consumes fuel during
         -- object initialization, and one that does not
src/MJ   -- MISSING
src/Experiments/Infer.agda


# Discrepancies

universe levels were omitted in the paper

MJSF: pattern matching lambdas are not useful for pattern matching
against, which we need in order to initialize method and field slots.
Instead of having the `All` with the pattern matching lambda, we use a
tagging predicate; e.g. `#m`.  This is morally equivalent to the `All`
used in the paper (Section 5.4).
