# 1.1.0

Minimal update to make the development compatible with Agda 2.6.1.1
and the corresponding version of the standard library.
Did not check support for 2.5.3, so may be backwards incompatible.

In the meantime the stdlib contains some of the things defined in this
library and in the stdlib extensions (formerly stdlib++).
We have not updated to use those definitions, but if you want to build on top of
this make sure to check out what the stdlib has to offer.

- stdlib++ no longer really exists. So inlined that library in the `src/`.
- Get rid of Data.List.Most
- Two functions that used to termination check no longer do, annotated with {-# TERMINATING #-}.
- Delete some unnecessary instances that messed up instance resolution in 2.6.1.1

# 1.0.0

Initial release with the paper for Agda 2.5.3
