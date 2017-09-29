# Contents

src/ScopeGraph

src/STLC
src/STLCRef
src/STLCSF
src/MJSF -- contains two semantics: one that consumes fuel during
         -- object initialization, and one that does not
src/MJ   -- MISSING
src/Experiments/Infer.agda


# Discrepancies with paper

universe levels were omitted in the paper

MJSF: pattern matching lambdas are not useful for pattern matching
against, which we need in order to initialize method and field slots.
Instead of having the `All` with the pattern matching lambda, we use a
tagging predicate; e.g. `#m`.  This is morally equivalent to the `All`
used in the paper (Section 5.4).

# Discrepancies with MJ

MJ distinguishes promotable expressions (method invocation and object
creation) and all other expressions.  We admit arbitrary expressions
to be promoted.  This does not change the semantics in any significant
way.  The expressions that we allow to be promoted are side-effect
free.

Returns are implemented by modeling non-void methods as having an
expression as its last statement (like in MJ).

MJ only has equality comparison expressions that can be used as
conditional expressions.  We allow arbitrary expressions, and use
`ifz`.  It would be straightforward to add booleans.

If statements have ordinary statements as their sub-statements.  These
can either be block statements or any other statement which does not
allocate a new frame.
